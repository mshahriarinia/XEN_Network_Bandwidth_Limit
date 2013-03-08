/******************************************************************************
 * arch/xen/drivers/netif/backend/common.h
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License version 2
 * as published by the Free Software Foundation; or, when distributed
 * separately from the Linux kernel or incorporated into other
 * software packages, subject to the following license:
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this source file (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software,
 * and to permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
 * IN THE SOFTWARE.
 */

#ifndef __NETIF__BACKEND__COMMON_H__
#define __NETIF__BACKEND__COMMON_H__

#include <linux/version.h>
#include <linux/module.h>
#include <linux/interrupt.h>
#include <linux/slab.h>
#include <linux/ip.h>
#include <linux/in.h>
#include <linux/netdevice.h>
#include <linux/etherdevice.h>
#include <linux/wait.h>
#include <xen/evtchn.h>
#include <xen/interface/io/netif.h>
#include <asm/io.h>
#include <asm/pgalloc.h>
#include <xen/interface/grant_table.h>
#include <xen/gnttab.h>
#include <xen/driver_util.h>
#include <xen/xenbus.h>

#define DPRINTK(_f, _a...)			\
	pr_debug("(file=%s, line=%d) " _f,	\
		 __FILE__ , __LINE__ , ## _a )
#define IPRINTK(fmt, args...)				\
	printk(KERN_INFO "xen_net: " fmt, ##args)
#define WPRINTK(fmt, args...)				\
	printk(KERN_WARNING "xen_net: " fmt, ##args)

struct backend_info;

struct xen_netif {
	/* Unique identifier for this interface. */
	domid_t          domid;
	unsigned int     handle;

	u8               fe_dev_addr[6];

	/* Physical parameters of the comms window. */
	grant_handle_t   tx_shmem_handle;
	grant_ref_t      tx_shmem_ref;
	grant_handle_t   rx_shmem_handle;
	grant_ref_t      rx_shmem_ref;
	unsigned int     irq;

	/* The shared rings and indexes. */
	struct xen_netif_tx_back_ring tx;
	struct xen_netif_rx_back_ring rx;
	struct vm_struct *tx_comms_area;
	struct vm_struct *rx_comms_area;

	/* Set of features that can be turned on in dev->features. */
	int features;

	/* Internal feature information. */
	u8 can_queue:1;	/* can queue packets for receiver? */
	u8 gso_prefix:1;	/* use a prefix segment for GSO information */
	u8 copying_receiver:1;	/* copy packets to receiver? */

	/* Allow netif_be_start_xmit() to peek ahead in the rx request
	 * ring.  This is a prediction of what rx_req_cons will be once
	 * all queued skbs are put on the ring. */
	RING_IDX rx_req_cons_peek;

	/* Transmit shaping: allow 'credit_bytes' every 'credit_usec'. */
	unsigned long   credit_bytes;
	unsigned long   credit_usec;
	unsigned long   remaining_credit;
	struct timer_list credit_timeout;

	/* Enforce draining of the transmit queue. */
	struct timer_list tx_queue_timeout;

	/* Statistics */
	int nr_copied_skbs;

	/* Miscellaneous private stuff. */
	struct list_head list;  /* scheduling list */
	atomic_t         refcnt;
	struct net_device *dev;
	struct net_device_stats stats;
	struct backend_info *be;

	unsigned int carrier;

	wait_queue_head_t waiting_to_free;
};

/*
 * Implement our own carrier flag: the network stack's version causes delays
 * when the carrier is re-enabled (in particular, dev_activate() may not
 * immediately be called, which can cause packet loss; also the etherbridge
 * can be rather lazy in activating its port).
 */
#define netback_carrier_on(netif)	((netif)->carrier = 1)
#define netback_carrier_off(netif)	((netif)->carrier = 0)
#define netback_carrier_ok(netif)	((netif)->carrier)

enum {
	NETBK_DONT_COPY_SKB,
	NETBK_DELAYED_COPY_SKB,
	NETBK_ALWAYS_COPY_SKB,
};

extern int netbk_copy_skb_mode;

/* Function pointers into netback accelerator plugin modules */
struct netback_accel_hooks {
	struct module *owner;
	int  (*probe)(struct xenbus_device *dev);
	int (*remove)(struct xenbus_device *dev);
};

/* Structure to track the state of a netback accelerator plugin */
struct netback_accelerator {
	struct list_head link;
	int id;
	char *eth_name;
	atomic_t use_count;
	struct netback_accel_hooks *hooks;
};

struct backend_info {
	struct xenbus_device *dev;
	struct xen_netif *netif;
	enum xenbus_state frontend_state;
	struct xenbus_watch hotplug_status_watch;
	struct xenbus_watch csum_offload_watch;
	int have_hotplug_status_watch:1;
	int have_csum_offload:1;
	int have_csum_offload_watch:1;

	/* State relating to the netback accelerator */
	void *netback_accel_priv;
	/* The accelerator that this backend is currently using */
	struct netback_accelerator *accelerator;
};

#define NETBACK_ACCEL_VERSION 0x00010001

/*
 * Connect an accelerator plugin module to netback.  Returns zero on
 * success, < 0 on error, > 0 (with highest version number supported)
 * if version mismatch.
 */
extern int netback_connect_accelerator(unsigned version,
				       int id, const char *eth_name,
				       struct netback_accel_hooks *hooks);
/* Disconnect a previously connected accelerator plugin module */
extern void netback_disconnect_accelerator(int id, const char *eth_name);


extern
void netback_probe_accelerators(struct backend_info *be,
				struct xenbus_device *dev);
extern
void netback_remove_accelerators(struct backend_info *be,
				 struct xenbus_device *dev);
extern
void netif_accel_init(void);


#define NET_TX_RING_SIZE __RING_SIZE((struct xen_netif_tx_sring *)0, PAGE_SIZE)
#define NET_RX_RING_SIZE __RING_SIZE((struct xen_netif_rx_sring *)0, PAGE_SIZE)

void netif_disconnect(struct xen_netif *netif);

struct xen_netif *netif_alloc(struct device *parent, domid_t domid, unsigned int handle);
int netif_map(struct xen_netif *netif, unsigned long tx_ring_ref,
	      unsigned long rx_ring_ref, unsigned int evtchn);

static inline void netif_get(struct xen_netif *netif)
{
	atomic_inc(&netif->refcnt);
}

static inline void  netif_put(struct xen_netif *netif)
{
	if (atomic_dec_and_test(&netif->refcnt))
		wake_up(&netif->waiting_to_free);
}

void netif_xenbus_init(void);

#define netif_schedulable(netif)				\
	(netif_running((netif)->dev) && netback_carrier_ok(netif))

void netif_schedule_work(struct xen_netif *netif);
void netif_deschedule_work(struct xen_netif *netif);

int netif_be_start_xmit(struct sk_buff *skb, struct net_device *dev);
struct net_device_stats *netif_be_get_stats(struct net_device *dev);
irqreturn_t netif_be_int(int irq, void *dev_id);

void netif_set_tx_csum(struct backend_info *, u32);

static inline int netbk_can_queue(struct net_device *dev)
{
	struct xen_netif *netif = netdev_priv(dev);
	return netif->can_queue;
}

static inline int netbk_can_sg(struct net_device *dev)
{
	struct xen_netif *netif = netdev_priv(dev);
	return netif->features & NETIF_F_SG;
}

#endif /* __NETIF__BACKEND__COMMON_H__ */
