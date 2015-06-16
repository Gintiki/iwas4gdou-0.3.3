#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <limits.h>
#include <unistd.h>
#include <time.h>
#include <getopt.h>
#include <signal.h>
#include <fcntl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/ioctl.h>
#include <sys/resource.h>
#include <net/if.h>
#include <netinet/if_ether.h>
#include <stdarg.h>
#include <pcap.h>
#include "global.h"
#include "pidfile.h"
#include "md5.h"
#include "rc4.h"

#define PSW_MAX      128
#define USR_MAX      64

#define ETHERNET_TYPE        0x88, 0x8e
#define EAE_GROUP_ADDRESS    0x01, 0x80, 0xC2, 0x00, 0x00, 0x03

#define PACKET_LEN          128
#define ERRBUF_LEN          PCAP_ERRBUF_SIZE + 128

#define IWAS4G_HWADDR_LEN    6

#define OUT_FILE    "/etc/iwas4gdou-%s"
#define PID_FILE    "/tmp/run/iwas4gdou-%s.pid"

unsigned char start[PACKET_LEN] = {
	EAE_GROUP_ADDRESS,    /* eth.dst        */
	0,0,0,0,0,0,              /* eth.src        */
	ETHERNET_TYPE,        /* eth.type       */
	0x01,                 /* eapol.version  */
	0x01,                 /* eapol.type     */
	0x00, 0x00            /* eapol.length   */
};

unsigned char reply_counter[8], key_iv[16], key_index;

struct bpf_program fp;

typedef struct {
  struct {
    unsigned char dst[IWAS4G_HWADDR_LEN];
    unsigned char src[IWAS4G_HWADDR_LEN];
    unsigned char type[2];
  } eth;
  struct {
    unsigned char version;
    unsigned char type;
    unsigned char length[2];
  } eapol;
  struct {
    unsigned char type;
    unsigned char key_length[2];
    unsigned char reply_counter[8];
    unsigned char key_iv[16];
    unsigned char key_index;
    unsigned char key_signature[16];
    unsigned char key[16];
  } keydes;
} pkt_eapol_key;

typedef struct {
  struct {
    unsigned char dst[IWAS4G_HWADDR_LEN];
    unsigned char src[IWAS4G_HWADDR_LEN];
    unsigned char type[2];
  } eth;
  struct {
    unsigned char version;
    unsigned char type;
    unsigned char length[2];
  } eapol;
  struct {
    unsigned char code;
    unsigned char id;
    unsigned char length[2];
    unsigned char type;
  } eap;
} pkt_eap_failure;

typedef struct {
  struct {
    unsigned char dst[IWAS4G_HWADDR_LEN];
    unsigned char src[IWAS4G_HWADDR_LEN];
    unsigned char type[2];
  } eth;
  struct {
    unsigned char version;
    unsigned char type;
    unsigned char length[2];
  } eapol;
  struct {
    unsigned char code;
    unsigned char id;
    unsigned char length[2];
    unsigned char type;
  } eap;
  unsigned char identity[PACKET_LEN - 23];
} pkt_eap_id;

typedef struct {
  struct {
    unsigned char dst[IWAS4G_HWADDR_LEN];
    unsigned char src[IWAS4G_HWADDR_LEN];
    unsigned char type[2];
  } eth;
  struct {
    unsigned char version;
    unsigned char type;
    unsigned char length[2];
  } eapol;
  struct {
    unsigned char code;
    unsigned char id;
    unsigned char length[2];
    unsigned char type;
  } eap;
  unsigned char value_size;
  unsigned char value[16];
  unsigned char identity[PACKET_LEN - 40];
} pkt_eap_md5ch;

char *if_name, *usr, *psw;
char pid_file[PATH_MAX];
char FilterStr[100];
pcap_t *sid = NULL;


unsigned char hw_addr[IWAS4G_HWADDR_LEN];

char error_buf[ERRBUF_LEN];

int deauth_mode = 0,c = 0;

static int get_opt (int argc, char **argv);
static void bind_device (char *if_name);
static void termination (int sig);
static int daemonize (void);
static void usage (void);

void send_eapol_logoff (void);

void send_id_respond(unsigned char id);
void send_md5ch_respond(unsigned char id,unsigned char chall[16]);
static void send_eapol_key (void);

static char * put_error (const char *fmt_str, ...);

static void pcap_handle(u_char *user,const struct pcap_pkthdr *h, const unsigned char *pkt);

static void iwas4g_watch(void);

void main (int argc, char **argv)
{
	time_t t;
	int old_pid;
	struct ifreq req;
	int errno, sinet;	

	if (get_opt(argc, argv)) { exit (-1);}

	sprintf(pid_file, PID_FILE, if_name);
	if (check_pid(pid_file)) {
		old_pid = read_pid(pid_file);
		if (deauth_mode) {
		kill(old_pid, SIGTERM);
		printf("De-authenticate.\n");
		} else {
			printf("iwas4gdou (%d) was already run on `%s'.\n",
				old_pid, if_name);
				exit (-1);
		}
	} else {
		remove_pid(pid_file);
	}

	sinet = socket(AF_INET, SOCK_DGRAM, 0);
	strcpy(req.ifr_name, if_name);
	errno = ioctl(sinet, SIOCGIFHWADDR, &req);
	close(sinet);
	if (errno != -1) {
		memcpy(hw_addr, req.ifr_hwaddr.sa_data, ETH_ALEN);
	}


		memcpy(start+6, hw_addr, 6);
		bind_device(if_name);
		pcap_sendpacket(sid, start, 18);
		pcap_loop (sid, -1, pcap_handle, NULL);
		if (!daemonize()) { 
			fprintf(stderr,"Running in background.\n");
		} else { fprintf(stderr,"Deamonizing fails.\n");}
		write_pid(pid_file);
		fprintf(stderr,"Edited by Con.\nEnjoy it o(^_^)o\n");
		time(&t);
		fprintf(stderr,"%s\n",ctime(&t));
		signal(SIGTERM, termination);
		iwas4g_watch();

}

static void
pcap_handle(u_char *user,const struct pcap_pkthdr *h,const unsigned char *pkt)
{


	char errbuf[ERRBUF_LEN];
	unsigned short eap_length;
	int i;
	unsigned char chall[16];

	if(pkt[15]==0x00){
		if(pkt[18]==0x01){
			switch(pkt[22]){
				case 0x01:
					send_id_respond(pkt[19]);
					break;
				case 0x04:
					for(i=0;i<16;i++){chall[i]=pkt[24+i];}
					send_md5ch_respond(pkt[19],chall);
					break;
				default:
					fprintf(stderr,"Unknown Packet.\n");
			}
		} else if (pkt[18]==0x03){
			sprintf(FilterStr, "ether src %02x:%02x:%02x:%02x:%02x:%02x && ether dst %02x:%02x:%02x:%02x:%02x:%02x && ether proto 0x888e", pkt[6],pkt[7],pkt[8],pkt[9],pkt[10],pkt[11],hw_addr[0], hw_addr[1], hw_addr[2], hw_addr[3], hw_addr[4], hw_addr[5]);
			pcap_compile(sid, &fp, FilterStr, 1, 0);
			pcap_setfilter(sid, &fp);
			fprintf(stderr,"Authentication succeeded.\n");
			pcap_breakloop(sid);
			
		} else if (pkt[18]==0x04){
			c++;
			eap_length = (((unsigned short)pkt[20]) << 8) + pkt[21];
			if (eap_length > 6) {
				sprintf(errbuf,"%s","Received [EAP-FAILURE] with message(GBK): [");
				i = strlen(errbuf);
				if ((i + eap_length - 6 + 3) <= ERRBUF_LEN) {
					memcpy(errbuf + i, pkt + 24, eap_length - 6);
					errbuf[(i + eap_length - 6)] = ']';
					errbuf[(++i + eap_length - 6)] = '.';
					errbuf[(++i + eap_length - 6)] = '\0';
				} else { strcat(errbuf, "...].");}
			} else { 
				sprintf(errbuf, "%s", "Received [EAP-FAILURE].");
			}
			put_error(errbuf);
			fprintf(stderr,"%s\n", error_buf);
			
			sleep(5);

			if(c>3){
				exit(-1);
			} else {
				pcap_sendpacket(sid, start, 18);
				return;
			}
			
		}
	return;
	}
	
}

void
send_id_respond(unsigned char id)
{
unsigned char usrlen = strlen(usr);
	
unsigned char id_respond[PACKET_LEN] = {
    EAE_GROUP_ADDRESS,    /* eth.dst        */
    0,0,0,0,0,0,          /* eth.src        */
    ETHERNET_TYPE,        /* eth.type       */
    0x01,                 /* eapol.version  */
    0x00,                 /* eapol.type     */
    0, 0,                 /* eapol.length   */
    0x02,                 /* eap.code       */
    0,                    /* eap.id         */
    0, 0,                 /* eap.length     */
    0x01,                 /* eap.type       */
    0                     /* eap.identity   */
};
pkt_eap_id *eap_id_respond = (pkt_eap_id *) &id_respond;
memcpy(id_respond+6, hw_addr, 6);
eap_id_respond->eapol.length[0] = (usrlen + 5) >> 8;
eap_id_respond->eapol.length[1] = (usrlen + 5);
eap_id_respond->eap.id = id;
eap_id_respond->eap.length[0] = eap_id_respond->eapol.length[0];
eap_id_respond->eap.length[1] = eap_id_respond->eapol.length[1];
memcpy(eap_id_respond->identity, usr, usrlen);
pcap_sendpacket(sid, id_respond, 23 + usrlen);

}

void
send_md5ch_respond(unsigned char id,unsigned char chall[16])
{
unsigned char md5ch_respond[PACKET_LEN] = {
	EAE_GROUP_ADDRESS,      /* eth.dst        */
	0,0,0,0,0,0,            /* eth.src        */
	ETHERNET_TYPE,          /* eth.type       */
	0x01,                   /* eapol.version  */
	0x00,                   /* eapol.type     */
	0, 0,                   /* eapol.length   */
	0x02,                   /* eap.code       */
	0,                      /* eap.id         */
	0, 0,                   /* eap.length     */
	0x04,                   /* eap.type       */
	0x10,                   /* eap.value-size           */
	0, 0, 0, 0, 0, 0, 0, 0, /* eap.value(hi-8byte)      */
	0, 0, 0, 0, 0, 0, 0, 0, /* eap.value(lo-8byte)      */
	0                       /* eap.extradata(identity)  */
};
pkt_eap_md5ch *eap_md5ch_respond = (pkt_eap_md5ch *) &md5ch_respond;
memcpy(md5ch_respond+6, hw_addr, 6);
unsigned char usrlen = strlen(usr);
unsigned char pswlen = strlen(psw);
MD5_CTX context;
char *srctext;
unsigned char digest[16];

srctext = (char *) malloc(17 + pswlen);
srctext[0] = id;
memcpy(srctext + 1, psw, pswlen);
memcpy(srctext + 1 + pswlen, chall, 16);
MD5Init(&context);
MD5Update(&context, (unsigned char *) srctext, 17 + pswlen);	
MD5Final(digest, &context);
free(srctext);
	
eap_md5ch_respond->eapol.length[0] = (usrlen + 22) >> 8;
eap_md5ch_respond->eapol.length[1] = (usrlen + 22);
eap_md5ch_respond->eap.id = id;
eap_md5ch_respond->eap.length[0] = eap_md5ch_respond->eapol.length[0];
eap_md5ch_respond->eap.length[1] = eap_md5ch_respond->eapol.length[1];
memcpy(eap_md5ch_respond->value, digest, 16);
memcpy(eap_md5ch_respond->identity, usr, usrlen);
pcap_sendpacket(sid, md5ch_respond, usrlen + 40);


}

int 
get_opt (int argc, char **argv)
{
  int opt;
  struct option long_opts[] = {
    {"help",          0,  NULL,  'h'},
    {"deauth",        0,  NULL,  'd'},
    {"interface",     1,  NULL,  'i'},
    {"user",          1,  NULL,  'u'},
    {"password",      1,  NULL,  'p'},
    {0, 0, 0, 0}
  };

  while ((opt = getopt_long(argc, argv, "hdai:u:p:rfc", long_opts, NULL)) 
         != -1) {
    switch (opt) {
      case '?':
      case 'h':
        usage();
        return (-1);

      case 'd':
	deauth_mode = 1;
	break;

      case 'i':
        if_name = optarg;
        break;

      case 'u':
        usr = optarg;
        if (strlen(usr) > USR_MAX) {
          printf(
            "User name is too long.\n");
          return (-1);
        }
        break;

      case 'p':
        psw = optarg;
        if (strlen(psw) > PSW_MAX) {
          printf( 
            "Password is too long.\n");
          return (-1);
        }
        break;

    }
  }
  
  return (0);
}


static void
bind_device (char *if_name)
{

  char errbuf[PCAP_ERRBUF_SIZE];

# define IF_NAME  "%s"



  /* Open interface by device name */

	sprintf(if_name, IF_NAME, if_name);
	sid = pcap_open_live(if_name, 80, 0, 0, errbuf);
	if (!sid) {fprintf(stderr,"Open device failed.\n");exit (-1);}

  /* Set capture filter */
	sprintf(FilterStr, "(ether proto 0x888e) and (ether dst %02x:%02x:%02x:%02x:%02x:%02x)",
		hw_addr[0], hw_addr[1], hw_addr[2], hw_addr[3], hw_addr[4], hw_addr[5]);
	if (!pcap_compile(sid, &fp, FilterStr, 1, 0)) {
		if (!pcap_setfilter(sid, &fp)) {
			fprintf(stderr,"Open device succeeded.\n");
		}
	} else {fprintf(stderr,"Open device failed.\n");exit (-1);}

}

static void 
termination (int sig)
{
  send_eapol_logoff ();
  pcap_breakloop(sid);
  pcap_close(sid);
  exit(0);
  /* signal(sig, SIG_DFL); */
}

static int 
daemonize(void)
{
  char out_file[PATH_MAX];
  int pid;

  pid = fork();
  if (pid == -1) {
    return (-1);
  } else if (pid != 0) {
    exit(0);
  }
  setsid();

  pid = fork();
  if (pid == -1) {
    return (-1);
  } else if (pid != 0) {
    exit(0);
  }

  close(0);
  close(1);
  close(2);
/* 日志记录 */
  open("/dev/null", O_RDWR);
  sprintf(out_file, OUT_FILE, if_name);
  open(out_file, O_WRONLY|O_CREAT|O_TRUNC, 0600);
  open(out_file, O_WRONLY|O_CREAT|O_TRUNC, 0600);
  chdir("/tmp");
  umask(0);
  return (0);
}


static void
usage (void)
{
#define USAGE "\
Usage: \n\
  iwas4gdou -d <-i interface> <-u user> [-p password]\n\n\
Examples: \n\
  # Authenticate\n\
  iwas4gdou -i eth0 -u zjlanhb302000 -p 02302000\n\n\
  # De-Authenticate\n\
  iwas4gdou -d\n\\"
  printf(USAGE);
}

static void
iwas4g_watch(void)
{
	time_t t;
	struct pcap_pkthdr *pkt_header;
	const unsigned char *pkt;
	const pkt_eapol_key *eapol_key;
	int i;
	unsigned short eap_length;
	char errbuf[ERRBUF_LEN];

	while(1)
	{
		while(pcap_next_ex(sid, &pkt_header, &pkt)>0){
		
			if (pkt[15] == 3 && pkt[18] == 1){
				eapol_key = (const pkt_eapol_key *) pkt;
				memcpy(reply_counter, eapol_key->keydes.reply_counter, 8);
				memcpy(key_iv, eapol_key->keydes.key_iv, 16);
				key_index = eapol_key->keydes.key_index;
				send_eapol_key();
				
			} else if (pkt[18]==0x04){
				eap_length = (((unsigned short)pkt[20]) << 8) + pkt[21];
				if (eap_length > 6) {
					sprintf(errbuf,"%s","Received [EAP-FAILURE] with message(GBK): [");
					i = strlen(errbuf);
					if ((i + eap_length - 6 + 3) <= ERRBUF_LEN) {
						memcpy(errbuf + i, pkt + 24, eap_length - 6);
						errbuf[(i + eap_length - 6)] = ']';
						errbuf[(++i + eap_length - 6)] = '.';
						errbuf[(++i + eap_length - 6)] = '\0';
					} else { strcat(errbuf, "...].");}
				} else { 
					sprintf(errbuf, "%s", "Received [EAP-FAILURE].");
				}
				put_error(errbuf);
				time(&t);
				
				fprintf(stderr,"%s\n",ctime(&t));
				sleep(5);
				pcap_sendpacket(sid, start, 18);
				pcap_loop (sid, 0, pcap_handle, NULL);
			}
		}
	}
}

static void
send_eapol_key (void)
{

struct rc4_state s;

  unsigned char pkt1[PACKET_LEN] = {
    EAE_GROUP_ADDRESS,      /* eth.dst        */
    0,0,0,0,0,0,                /* eth.src        */
    ETHERNET_TYPE,          /* eth.type       */
    0x01,                   /* eapol.version  */
    0x03,                   /* eapol.type     */
    0x00, 0x3C,             /* eapol.length   */
    0x01,                                             /* keydes.type          */
    0x00, 0x10,                                       /* keydes.key_length    */
    0, 0, 0, 0, 0, 0, 0, 0,                           /* keydes.reply_counter */
    0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,  /* keydes.key_iv        */
    0,                                                /* keydes.key_index     */
    0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,  /* keydes.key_signature */
    0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0   /* keydes.key           */
  };
  unsigned char pkt2[PACKET_LEN] = {
    EAE_GROUP_ADDRESS,      /* eth.dst        */
    0,0,0,0,0,0,            /* eth.src        */
    ETHERNET_TYPE,          /* eth.type       */
    0x01,                   /* eapol.version  */
    0x03,                   /* eapol.type     */
    0x00, 0x30,             /* eapol.length   */
    0x01,                                             /* keydes.type          */
    0x00, 0x04,                                       /* keydes.key_length    */
    0, 0, 0, 0, 0, 0, 0, 0,                           /* keydes.reply_counter */
    0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,  /* keydes.key_iv        */
    0,                                                /* keydes.key_index     */
    0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,  /* keydes.key_signature */
    0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0   /* keydes.key           */
  };

  pkt_eapol_key *eapol_key1 = (pkt_eapol_key *) &pkt1;
  pkt_eapol_key *eapol_key2 = (pkt_eapol_key *) &pkt2;

  memcpy(pkt1+6, hw_addr, 6);
  memcpy(pkt2+6, hw_addr, 6);

  unsigned char new_key_iv[20];
  unsigned char session_key1[16] = {
	   0x02,0x0E,0x05,0x04,0xf2,0x90,0x00,0x0a,
	   0x06,0x06,0x98,0xf5,0x37,0x42,0x26,0x96};
  unsigned char session_key2[4]  = {0x02, 0x02, 0x14, 0x00};

  /* Generate a `new key iv' by concatenating:
   * received `key iv' and its `lower-4bytes' */
  memcpy(new_key_iv, key_iv, 16);
  memcpy(new_key_iv + 16, new_key_iv + 12, 4);

  /* Generate RC4 crypt stream and 1st/2nd session key */
  rc4_setup(&s, new_key_iv, 20);
  rc4_crypt(&s, session_key1, 16);
  rc4_crypt(&s, session_key2, 4);

  /* Fill 1st/2nd [EAPOL-KEY] */
  memcpy(eapol_key1->keydes.reply_counter, reply_counter, 8);
  memcpy(eapol_key1->keydes.key_iv, key_iv, 16);
  eapol_key1->keydes.key_index = key_index;
  memcpy(eapol_key1->keydes.key, session_key1, 16);
  hmac_md5(
    &eapol_key1->eapol.version, 64, 
    &eapol_key1->keydes.key_index, 1, 
    eapol_key1->keydes.key_signature);

  memcpy(eapol_key2->keydes.reply_counter, reply_counter, 8);
  memcpy(eapol_key2->keydes.key_iv, key_iv, 16);
  eapol_key2->keydes.key_index = key_index;
  memcpy(eapol_key2->keydes.key, session_key2, 4);
  hmac_md5(
    &eapol_key2->eapol.version, 52, 
    &eapol_key2->keydes.key_index, 1, 
    eapol_key2->keydes.key_signature);
  
  /* send 1st [EAPOL-KEY] */
pcap_sendpacket(sid, pkt1, 78);
pcap_sendpacket(sid, pkt2, 66);
}

void
send_eapol_logoff (void)
{
  unsigned char pkt[PACKET_LEN] = {
    EAE_GROUP_ADDRESS,    /* eth.dst        */
    0,0,0,0,0,0,              /* eth.src        */
    ETHERNET_TYPE,        /* eth.type       */
    0x01,                 /* eapol.version  */
    0x02,                 /* eapol.type     */
    0x00, 0x00,           /* eapol.length   */
  };
memcpy(pkt+6, hw_addr, 6);
  if(sid) {
    pcap_sendpacket(sid, pkt, 18);
  }
}

static char *
put_error (const char *fmt_str, ...)
{
  va_list args;

  va_start(args, fmt_str);
  vsprintf(error_buf, fmt_str, args);
  va_end(args);
  return error_buf;
}
