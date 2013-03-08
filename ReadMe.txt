
This project involves doing the following things:
1) Add the "rates" bytes and usec pair to the Xenbus for the vif devices
2) verify that these rates are enforced by the backend credit mechanism
3) Make a script or program to run on Dom0 that allows the available
bandwidth to be partitioned between the different VMs based on a percentage
of available bandwidth
4) Use this script to punish a rogue VM by lowering its bandwidth allocation
to a small positive percentage (it cannot be stopped completely because zero
values are interpreted as "unlimited" by the kernel)

Richard



 