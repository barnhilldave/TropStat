#########################################################################
## Author :  Ruriko Yoshida and David Barnhill                         ##
## Date   :  March 26th 2022                                           ##
## Update :  Mark 1st 2023.                                            ##
## Program:  These functions are used for investigating                ##
##           characteristics of tropical polytopes and                 ##
##           data derivatives.                                         ##
#########################################################################
library(MASS)
library(ape)
library(phangorn)
library(lpSolve)
library(lpSolveAPI)
library("miscTools")
library(Matrix)
library(rcdd)
library( rgl )
library(magick)
library(gtools)
library(combinat)
library(RcppAlgos)
library(Rfast)

printf <- function(...) invisible(print(sprintf(...)))



# This function is used for calculating R-Square
fermatweberdistance <- function(datamatrix) {
  n = dim(datamatrix)[1]
  print(n)
  m = dim(datamatrix)[2]
  lprec <- make.lp(0, n+m)
  objective = mat.or.vec(n+m,1)
  for (i in seq(n)) {
    objective[i] = 1
  }
  set.objfn(lprec, objective)
  for (i in seq(n)) {
    for (j in seq(m)) {
      for (k in seq(m)) {
        v = mat.or.vec(n+m,1)
        v[i] = 1
        v[n+k] = 1
        v[n+j] = -1
        add.constraint(lprec, v, ">=", datamatrix[i,k] - datamatrix[i,j])
      }
    }
  }
  solve(lprec)
  return((get.variables(lprec)))
}

trop.dist <- function(D1, D2){
  return(max(D2 - D1) - min(D2 - D1))
}

normaliz.tree <- function(D, h = 1){
  d <- length(D)
  a <- max(D) - h
  x <- D - rep(a, d)
  for(i in 1:d)
    if(x[i] < 0)
      x[i] <- 0
  return(x)
}

### The first coordinate must be 0.
normaliz.vector <- function(D){
  return(D - rep(D[1], length(D)))
}

normaliz.vectors <- function(DD){ ## DD is a matrix
  d <- dim(DD)
  D1 <- DD
  for(i in 1:d[1])
    D1[i, ] <- D1[i, ] - rep(D1[i, 1], d[2])
  return(D1)
}

normaliz.polytope <- function(M){
  d <- dim(M)
  for(i in 1:d[1])
    M[i, ] <- normaliz.vector(M[i,])
  return(M)
}


TLineSeg <- function(D1, D2){
  d <- length(D1)
  if(length(D1) != length(D2))
    warning("dimension is wrong!")
  index <- order(D2 - D1)
  lambda <- (D2 - D1)[index]
  x1 <- rep(0, d)
  segment <- list()
  for(j in 1:d){
    for(i in 1:d){
      x1[i] <- 0
      x1[i] <- max(lambda[j] + D1[i], D2[i])
    }
    segment[[j]] <- x1
  }
  return(segment)
}

TLineSeg_min <- function(D1, D2){
  d <- length(D1)
  if(length(D1) != length(D2))
    warning("dimension is wrong!")
  index <- order(D2 - D1,decreasing = TRUE)
  lambda <- (D2 - D1)[index]
  x1 <- rep(0, d)
  segment <- list()
  for(j in 1:d){
    for(i in 1:d){
      x1[i] <- 0
      x1[i] <- min(lambda[j] + D1[i], D2[i])
    }
    segment[[j]] <- normaliz.vector(x1)
  }
  return(segment)
}


Points.TLineSeg <- function(D1, D2, k = 20){
  d <- length(D1)
  x <- matrix(rep(0, d*k), k, d)
  if(length(D1) != length(D2))
    warning("dimension is wrong!")
  index <- order(D2 - D1)
  lambda <- (D2 - D1)[index]
  L <- lambda[d] - lambda[1]
  l <- runif(1, min=lambda[1], max=lambda[d])
  for(j in 1:(k-1))
    for(i in 1:d){
      x[j, i] <- max((lambda[1] + (j * L)/k) + D1[i], D2[i])
    }

  return(x)
}

######## Uniformly Sample over a tropical line segment ############

HAR.TLineSeg <- function(D1, D2){
  d <- length(D1)
  if(length(D1) != length(D2))
    warning("dimension is wrong!")
  index <- order(D2 - D1)
  lambda <- (D2 - D1)[index]
  l <- runif(1, min=lambda[1], max=lambda[d])
  x1 <- rep(0, d)

  for(i in 1:d){
    x1[i] <- max(l + D1[i], D2[i])
  }

  return(x1)
}

######## Gaussian Sampler over a tropical line segment ############

HAR.TLineSeg.Norm <- function(D1, D2,mu,stdev){
  d <- length(D1)
  D<-rbind(D1,D2)
  if(length(D1) != length(D2))
    warning("dimension is wrong!")
  proj_mu<-project_pi(D,mu)
  l0<-trop.dist(D1,proj_mu)+min(D1-D2)
  pro_true<-FALSE
  while(pro_true==FALSE){
    l <- rnorm(1, mean = 0, sd=stdev)
    x_p <- rep(0, d)
    for(i in 1:d){
      x_p[i] <-max(((l0+l) + D2[i]), D1[i])
    }
    pro_x<-project_pi(D,x_p)
    dist_pro<-trop.dist(x_p,pro_x)
    if(dist_pro<=1e-8){
      x1<-normaliz.vector(x_p)
      pro_true<-TRUE
    }
  }
  return(x1)
}


#### HAR on a tropical polytope

project_pi<-function(D_s,D){
  d <- dim(D_s)
  lambda <- rep(0, d[1])
  for(i in 1:d[1])
    lambda[i] <- min(D - D_s[i,])

  x <- rep(0, d[2])
  for(i in 1:d[2])
    x[i] <- max((lambda+D_s)[, i])
  return(normaliz.vector(x))
}


sample.pi <- function(D_s, a, b){
  d <- dim(D_s)
  #index <- sample(1:d[1], 1)
  lambda <- rep(0, d[1])
  #lambda[index] <- runif(1, min=a, max=b)
  for(i in 1:d[1])
    lambda[i] <- runif(1, min=a[i], max=b[i])
  #for(i in 1:d[1])
  #    lambda[i] <- min(D - D_s[i,])

  x <- rep(0, d[2])
  for(i in 1:d[2])
    x[i] <- max((lambda+D_s)[, i])
  return(x)
}


### Input: rxd matrix and each row of the matrix is a vertex of the polytope.
Intervals <- function(D_s){
  d <- dim(D_s)
  L <- matrix(rep(0, d[1]*d[2]), d[2], d[1])
  for(i in 2:d[2])
    L[i, i] <- max(D_s[1,] - D_s[i,])
  for(j in 1:d[2]){
    for(k in 2:d[1]){
      if(k != j){
        L[j, k] <- L[j, j] - max(D_s[k,] - D_s[j,])
      }
    }
  }
  # print(L)
  bounds <- matrix(rep(0, 2*d[1]), 2, d[1])
  for(i in 1:d[1])
    bounds[1, i] <- min(L[,i])
  for(i in 1:d[1])
    bounds[2, i] <- max(L[,i])
  return(bounds)
}



#### HAR algorithm on the space of ultrametrics
### n is the number of leaves

Ultrametrics.HAR <- function(x0, n, I = 1, h = 1){
  d <- length(x0)
  x <- normaliz.tree(x0, h)
  a <- h

  for(i in 1:I){
    x1 <- normaliz.tree(x, h)
    D0 <- symMatrix(runif(choose((n+1), 2), 0, a), n)
    for(k in 1:n)
      D0[k, k] <- 0
    tree <- upgma(D0)
    #tree <- rcoal(n)
    tree$edge.length <- tree$edge.length/max(tree$edge.length)
    D <- cophenetic(tree)
    v <- D[lower.tri(t(D))] #rep(0, d)
    #t <- 1
    #for(ii in 1:(n-1))
    #    for(jj in (ii+1):n){
    #        v[t] <- D[ii, jj]
    #        t <- t + 1
    #    }
    x <- HAR.TLineSeg(normaliz.tree(x1, h), normaliz.tree(v, h))
  }

  return(normaliz.tree(x, h))
}




### D is the set of vertices for tropical polytope with row is a vertex
### Only for e = 4.
pre.draw.tpolytope.3d <- function(D, v,c){
  d <- dim(D)
  seg <- matrix(rep(0, 3*choose(d[1], 2)*(2*3)), 3*choose(d[1], 2), 6)
  counter <- 1
  for(i in 1:(d[1] - 1)){
    for(j in (i+1):d[1]){
      t <- TLineSeg(D[i, ], D[j, ])
      for(k in 1:3){
        seg[counter, 1:3] <- normaliz.vector(t[[k]])[2:4]
        seg[counter, 4:6] <- normaliz.vector(t[[k+1]])[2:4]
        counter <- counter + 1
      }
    }
  }

  segments3d(x=as.vector(t(seg[1:(counter-1), c(1,4)])),
             y=as.vector(t(seg[1:(counter-1), c(2,5)])),
             z=as.vector(t(seg[1:(counter-1), c(3,6)])), col = c, lwd = .2,tcl=-.9)
  for(i in 1:v)
    spheres3d(D[i, 2:4], r = 0.1, color = "black")
  #rgl.points(D[i, 2:4], color = "blue", size = 10)

  axes3d()
  title3d(xlab="X",ylab="Y",zlab="Z")
}

draw.tpolytope.3d <- function(D,c){
  d <- dim(D)
  D1 <- D
  for(i in 1:(d[1] - 1)){
    for(j in (i+1):d[1]){
      M <- Points.TLineSeg(D[i, ], D[j, ])
      D1 <- rbind(D1, M)
    }
  }
  pre.draw.tpolytope.3d(D1, d[1],c)

}

###### Check whether x is in a tropical polytope P or not.

Check.onto.Tpoly <- function(D_s, x){
  ### D_s is a set of vertices for a tropical polytope.
  ### Each row of D_s is a vertex of the tropical polytope.
  ### We would like to check whether x is on the tropical polytope or not.
  ### If x is on the tropical polytope then it returns 1.  If not it returns 0.
  y <- project_pi(D_s, x)
  res <- 0
  if(trop.dist(x, y) == 0) res <- 1
  return(res)
}

##### Sampling from Gaussian using Metropolis Hastings Filter #####
### mu: center of mass
### D: set of vertices of a tropical polytope
### s: standard deviation
### I: number of iterations
trop.Gaussian <- function(D, x0,mu, s, n){

  d <- dim(D)
  mu <- normaliz.vector(mu)
  N <- matrix(rep(0, n*d[2]), n, d[2])
  #x0 <- mu
  i <- 1
  while(i <= n){
    print(i)
    x1 <- TropicalPolytope.V.HAR(D, x0, I = 50, k = 3)
    #x1 <- TropicalPolytope.extrapolation.HAR_v4(D, x0, I = 50,k=3)
    x1 <- normaliz.vector(x1)
    (r <- exp(-trop.dist(mu, x1)^2/s)/exp(-trop.dist(mu, x0)^2/s))
    #r<-exp(-trop.dist(mu, x1)/s)/exp(-trop.dist(mu, x0)/s)
    if(runif(1) < r){
      x0 <- x1
      N[i, ] <- x0
      N[i, ] <-  normaliz.vector(N[i, ])
      i <- i + 1
    }
  }
  return(N)
}


############################################################################################
## Author :  David Barnhill
## Date   :  October 12th 2022
## Program:  This code produces a tropical ball in two or three dimensions
## Input  :  Central point, v; tropical radius of ball; color to use for lines or
##           shading shading level (Defaults to black); of each side, a, (1 equals opaque);
##           fill logical indicating whether to fill each facet with color.
##           If fill is 'TRUE' then then the one dimensional facets (line segments)
##           show (Default is FALSE); plot logical indicating whether to
##           execute a new plot of the ball or to plot it on an existing
##           plot (Default is TRUE); border for 2D plots (Default is black).
##           For 2D plots, if a plot is not already open, plot must be TRUE.
##           For 3D plots, new plot is not necessary.
##           Either way, if a plot is already present, set plot to 'FALSE' and
##           the ball will overlay on the current plot.
## Output :  Plot or overlay of Euclidean representaiton oftropical ball in 2D or 3D.
## Execute: type in R as
##
#########################################################################################

Trop_ball<-function(v,d,a=1,cls='black',cent.col='black',fil=TRUE,plt=TRUE,bord='black'){
  dm<-length(v)-1
  if(dm==2){
    if (plt==TRUE){
      plot(v[2],v[3],type='n',xlim =c(v[2]-d-.25,(v[2]+d+.25)) ,
           ylim =c(v[3]-d-.25,(v[3]+d+.25)) ,
           xlab='x2',ylab='x3',asp=1)
    }
    polygon(c(v[2]-d,v[2]-d,v[2],v[2]+d,v[2]+d,v[2]),c(v[3]-d,v[3],v[3]+d,v[3]+d,v[3],v[3]-d),col=cls,density=70,border = bord,lwd=2)
    points(v[2],v[3],pch=19,col=cent.col)
  }

  if(dm==3){
    if (plt==TRUE){
      plot3d(v[2],v[3],v[4],pch=19,col=cent.col,size=6,xlim =c(v[2]-d-.25,(v[2]+d+.25)) ,
             ylim =c(v[3]-d-.25,(v[3]+d+.25)) ,
             zlim=c(v[4]-d-.25,(v[4]+d+.25)),
             xlab='x2',ylab='x3',zlab='x4',asp=1)
    }

    polygon3d(c(v[2]-d,v[2]-d,v[2]-d,v[2]-d),c(v[3],v[3]-d,v[3]-d,v[3]),c(v[4],v[4],v[4]-d,v[4]-d),
              coords = c(2,3),fill = fil,alpha=a,col=cls)
    polygon3d(c(v[2],v[2]-d,v[2]-d,v[2]),c(v[3]-d,v[3]-d,v[3]-d,v[3]-d),c(v[4],v[4],v[4]-d,v[4]-d),
              coords = c(1,3),fill = fil,alpha=a,col=cls)
    polygon3d(c(v[2],v[2]-d,v[2]-d,v[2]),c(v[3],v[3],v[3]-d,v[3]-d),c(v[4]-d,v[4]-d,v[4]-d,v[4]-d),
              coords = c(1,2),fill = fil,alpha=a,col=cls)
    polygon3d(c(v[2]+d,v[2]+d,v[2]+d,v[2]+d),c(v[3],v[3]+d,v[3]+d,v[3]),c(v[4],v[4],v[4]+d,v[4]+d),
              coords = c(2,3),fill = fil,alpha=a,col=cls)
    polygon3d(c(v[2],v[2]+d,v[2]+d,v[2]),c(v[3]+d,v[3]+d,v[3]+d,v[3]+d),c(v[4],v[4],v[4]+d,v[4]+d),
              coords = c(1,3),fill = fil,alpha=a,col=cls)
    polygon3d(c(v[2],v[2]+d,v[2]+d,v[2]),c(v[3],v[3],v[3]+d,v[3]+d),c(v[4]+d,v[4]+d,v[4]+d,v[4]+d),
              coords = c(1,2),fill = fil,alpha=a,col=cls)
    polygon3d(c(v[2]-d,v[2],v[2],v[2]-d),c(v[3],v[3]+d,v[3]+d,v[3]),c(v[4],v[4]+d,v[4],v[4]-d),
              coords = c(2,3),fill = fil,alpha=a,col=cls)
    polygon3d(c(v[2]-d,v[2],v[2],v[2]-d),c(v[3],v[3]+d,v[3],v[3]-d),c(v[4],v[4]+d,v[4]+d,v[4]),
              coords = c(2,3),fill = fil,alpha=a,col=cls)
    polygon3d(c(v[2]-d,v[2],v[2]+d,v[2]),c(v[3]-d,v[3],v[3],v[3]-d),c(v[4],v[4]+d,v[4]+d,v[4]),
              coords = c(1,2),fill = fil,alpha=a,col=cls)
    polygon3d(c(v[2],v[2]+d,v[2]+d,v[2]),c(v[3]-d,v[3],v[3],v[3]-d),c(v[4],v[4]+d,v[4],v[4]-d),
              coords = c(2,3),fill = fil,alpha=a,col=cls)
    polygon3d(c(v[2],v[2],v[2]+d,v[2]+d),c(v[3]-d,v[3],v[3]+d,v[3]),c(v[4]-d,v[4]-d,v[4],v[4]),
              coords = c(2,3),fill = fil,alpha=a,col=cls)
    polygon3d(c(v[2]-d,v[2],v[2]+d,v[2]),c(v[3],v[3],v[3]+d,v[3]+d),c(v[4]-d,v[4]-d,v[4],v[4]),
              coords = c(1,2),fill = fil,alpha=a,col=cls)
    if (plt==FALSE){
      points3d(v[2],v[3],v[4],pch=19,col='white',size=6)
    }
  }
}


#### Calculate distance from a point to a max hyperplane ####
trop.dist.hyp_max<-function(O,bp){
  x<-O+bp
  x_prime<-x[order(x,decreasing = TRUE)]
  dist<-x_prime[1]-x_prime[2]
  return(dist)
}

#### Calculate distance from a point to a min hyperplane ####
trop.dist.hyp_min<-function(O,bp){
  x<-O+bp
  x_prime<-x[order(x,decreasing = FALSE)]
  (dist<-x_prime[2]-x_prime[1])
  return(dist)
}

#### HAR Extrapolation with fixed nu. Used for polytropes ######
# Input: Vertices of polytope, D_s; starting point, x0; number #
# of steps, I; cardinality, k, of subset, U.                   #
# Output: Point x1 in polytope                                 #
################################################################

TropicalPolytope.extrapolation.HAR_v4 <- function(D_s, x0, I = 1,k=1){
  d <- dim(D_s) # dimension of matrix of vertices
  D <- normaliz.polytope(D_s) #D_s
  D_bp<-D
  x <- normaliz.vector(x0) #normalize x0

  for(i in 1:I){
    x1 <- x
    v <- x
    u <- x
    ind<-seq(1,d[1])
    (index <- sample(ind, k)) # Randomly choose k vertices
    U <- D[index,] # Subset U
    V <- D[-index,] # Complement of U
    if(k == 1) # If subset k=1 then this is just a vertex
      u <- U   # the projection of x0 on a vertex is just the vertex
    else{
      u <- project_pi(U, x1) # If k>1 project x0 onto the polytope
    }                      # defined by the subset of vertices
    if(k == (d[1] - 1)) # If the cardinality of U is e-1
      v <- V            # the complement is just the leftover vertex
    else
      v <- project_pi(V, x1) # Otherwise it is a projection
    Gam<-unique(TLineSeg(v,u)) # Get unique bendpoints in a tropical line
    bps<-normaliz.polytope(matrix(unlist(Gam),length(Gam),d[2],byrow=TRUE)) # Normalize the bendpoints
    # We calculate the tropical distance of the bendpoints (not the end points) of the tropical
    # line segment to each boundary vertex defining a hyperplane.
    # If there is more than one bendpoint, calculate the distance of each one.  If not then just
    # conduct HAR on the line segment.
    if(nrow(bps)>2){
      l<-matrix(u,1,ncol(bps),TRUE) # Matrix only consisting of the starting point.
      bp<-bps[2:(nrow(bps)),] # bendpoints of the line segment without the endpoints
      t=0
      while (t <nrow(bp)){
        t=t+1
        dists<-as.vector(apply(D,1,function(x) trop.dist.hyp_min(-x,bp[t,]))) # Calculates distance of bend point to all vertices
        if(all(dists>1e-8)){
          l<-rbind(l,bp[t,])
        }
        else{
          l<-rbind(l,bp[t,]) # If there is a zero add the point and then exit the loop.
          break
        }
      }
      x<-HAR.TLineSeg(l[1,], l[nrow(l),]) # Conduct HAR on line segment between u and the last bendpoint.
      x<-normaliz.vector(x)
    }
    else{
      x<-HAR.TLineSeg(u,v) # Conduct HAR if there are no bendpoints.
      x<-normaliz.vector(x)
    }
  }

  return(normaliz.vector(x))
}

#### Gaussian HAR Sampler over a tropical line segment #####################
# Helper function for the normal extrapolation algorithm                   #
# Input: End points of a line segment D1 and D2; center of mass point mu.  #
# on the line segment; standard deviation, stdev, associated with proximity#
# to mu.                                                                   #
# Output: Point x1 on line segment over the interval of projected points.  #
# that are the projections of mu on the line segment.                      #
############################################################################

HAR.TLineSeg.Norm_Poly<-function(D1,D2,mu,stdev){
  d <- length(D1)
  D<-rbind(D1,D2)
  if(length(D1) != length(D2))
    warning("dimension is wrong!")
  proj_mu<-project_pi(D,mu)
  d_mu<-trop.dist(mu,proj_mu)
  d_hi<-1000
  d_lo<-1000
  E_hi<-D2
  E_lo<-D1
  while(d_hi>(d_mu+1e-8)){
    prop<-HAR.TLineSeg(E_hi,proj_mu)
    d_hi<-trop.dist(prop,mu)
    E_hi<-normaliz.vector(prop)
  }
  while(d_lo>(d_mu+1e-8)){
    prop<-HAR.TLineSeg(E_lo,proj_mu)
    d_lo<-trop.dist(prop,mu)
    E_lo<-normaliz.vector(prop)
  }
  pro_mu<-HAR.TLineSeg(E_hi,E_lo)
  pts<-rbind(D1,D2,pro_mu)
  l0<-trop.dist(D2,pro_mu)+min(D2-D1)
  l <- rnorm(1, mean = 0, sd=stdev)
  #print(l)
  x_p <- rep(0, d)
  for(i in 1:d){
    x_p[i] <-max(((l+ l0) + D1[i]), D2[i])
  }
  x1<-normaliz.vector(x_p)
  return(x1)
}

#### HAR Extrapolation with Gaussian sampling over a tropical polytope######
# Input: Vertices of polytope, D_s; starting point, x0; number             #
# of steps, I; cardinality, k, of subset, U; center of mass point M;       #
# standard deviation S associated with a scalar lambda.                    #
# Output: Point x1 in polytope                                             #
############################################################################

TropicalPolytope.extrapolation.HAR_NORM <- function(D_s, x0, I = 1,k=1,M,S){
  d <- dim(D_s) # dimension of matrix of vertices
  D <- normaliz.polytope(D_s) #D_s
  D_bp<-D
  x <- normaliz.vector(x0) #normalize x0

  for(i in 1:I){
    x1 <- x
    v <- x
    u <- x
    ind<-seq(1,d[1])
    (index <- sample(ind, k)) # Randomly choose k vertices
    U <- D[index,] # Subset U
    V <- D[-index,] # Complement of U
    if(k == 1) # If subset k=1 then this is just a vertex
      u <- U   # the projection of x0 on a vertex is just the vertex
    else{
      u <- project_pi(U, x1) # If k>1 project x0 onto the polytope
    }                      # defined by the subset of vertices
    if(k == (d[1] - 1)) # If the cardinality of U is e-1
      v <- V            # the complement is just the leftover vertex
    else
      v <- project_pi(V, x1) # Otherwise it is a projection
    Gam<-unique(TLineSeg(v,u)) # Get unique bendpoints in a tropical line
    bps<-normaliz.polytope(matrix(unlist(Gam),length(Gam),d[2],byrow=TRUE)) # Normalize the bendpoints
    # We calculate the tropical distance of the bendpoints (not the end points) of the tropical
    # line segment to each boundary vertex defining a hyperplane.
    # If there is more than one bendpoint, calculate the distance of each one.  If not then just
    # conduct HAR on the line segment.
    if(nrow(bps)>2){
      l<-matrix(u,1,ncol(bps),TRUE) # Matrix only consisting of the starting point.
      bp<-bps[2:(nrow(bps)),] # bendpoints of the line segment without the endpoints
      t=0
      while (t <nrow(bp)){
        t=t+1
        dists<-as.vector(apply(D,1,function(x) trop.dist.hyp_min(-x,bp[t,]))) # Calculates distance of bend point to all vertices
        if(all(dists>1e-8)){
          l<-rbind(l,bp[t,])
        }
        else{
          l<-rbind(l,bp[t,]) # If there is a zero add the point and then exit the loop.
          break
        }
      }
      x<-HAR.TLineSeg.Norm_Poly(l[1,], l[nrow(l),],mu,s) # Conduct HAR on line segment between u and the last bendpoint.
      x<-normaliz.vector(x)
    }
    else{
      x<-HAR.TLineSeg.Norm_Poly(u,v,mu,s) # Conduct HAR if there are no bendpoints.
      x<-normaliz.vector(x)
    }
  }

  return(normaliz.vector(x))
}




####### Tropical Ball Vertices #################################################
# Given a point, x in R^e/R1 which representing the center of a tropical ball. #
# Calculate the vertices defining the tropical convex hull of the tropical.    #
# ball.                                                                        #
# Input: x0 in R^e/R1                                                          #
# Output: R^(e x e) matrix representing tropical convex hull                   #
################################################################################
trop_bal.vert<-function(x,d,dm){
  A<-matrix(0,dm,dm,TRUE)
  i=1
  while (i < dm){
    i=i+1
    a<-c(rep(0,dm))
    a[i]<-d
    A[i,]<-x+a
  }
  A[1,]<-x-c(0,rep(d,(dm-1)))
  return(A)
}

####### Volume of a Tropical Polytope ##########################################
# Given a minimum enclosing tropical ball, B, with radius, R, surrounding a    #
# tropical polytope, P, sample from B and determine the proportion of points.  #
# that fall inside B and P.  Multiply this proportion by the volume of B to    #
# calculate the volume of P.
# Input: Minimum encompassing ball, B; convex hull of tropical polytope, P;    #
#        starting point x0; sample size, S; iterations for HAR algorithm,i;    #
#        dimension of polytope P in R^d/R1, d; radius of B, R.                 #
# Output (list): ratio of points in P to S; Volume of the tropical ball, B;    #
#                Volume of P;      #
################################################################################
Trop_Volume<-function(B,P,x0,S,i,d=ncol(P),R){
  count<-0
  #har_points<-matrix(0,S,d,TRUE)
  #har_points1<-matrix(0,0,d)
  for (i in (1:S)){
    print(i)
    x<-TropicalPolytope.extrapolation.HAR_v4(B, x0, I = i,k=(d-1))
    proj<-project_pi(P,x)
    if(trop.dist(x,proj)<=1e-8){
      count<-count+1
      #har_points1<-rbind(har_points1,x)
    }
    #har_points[i,]<-x
    x0<-x
  }
  r<-count/S
  VolB<-(d)*R^(d-1)
  VolP<-r*VolB
  return(list(r,VolB,VolP))
}

##########Drawing 3D hyperplanes for a given set of vertices ############
## Author :  David Barnhill                                            ##
## Date   :  November 21st 2022                                        ##
## Program:  This code produces the 3D tropical min-plus hyperplanes   ##
##           for a given set of vertices defining a tropical polytope. ##
## Input  :  A matrix, D, of vertices; maximum length, di; minimum     ##
##           value for each coordinate axis, mi; maximum value for each##
##           coordinate axis, ma; logical to determine whether to plot.##
## Output :  Plot of min-plus hyperplane defining a tropical polytope. ##
## Execute:  type in R as                                              ##
#########################################################################

hyper3d_min<-function(D,di,mi,ma,plt=FALSE){
  cl<-rainbow(nrow(D))
  d<-dim(D)
  if((d[2]-1)==3){
    if(plt==TRUE){
      plot3d(D[,2],D[,3],D[,4],type='n',xlim=c(mi,ma),ylim=c(mi,ma),zlim=c(mi,ma),xlab='x2',ylab = 'x3',zlab='x4',asp=1)
    }
    for (i in 1:(nrow(D))){
      x<-D[i,]
      xs1<-c(x[2],x[2]-di,x[2]-di,x[2])
      ys1<-c(x[3],x[3]-di,x[3]-di,x[3])
      zs1<-c(x[4],x[4]-di,x[4]+di,x[4]+di)

      xs2<-c(x[2],x[2]-di,x[2]-di,x[2])
      ys2<-c(x[3],x[3]-di,x[3]+di,x[3]+di)
      zs2<-c(x[4],x[4]-di,x[4]-di,x[4])

      xs3<-c(x[2],x[2]-di,x[2]+di,x[2]+di)
      ys3<-c(x[3],x[3]-di,x[3]-di,x[3])
      zs3<-c(x[4],x[4]-di,x[4]-di,x[4])

      xs4<-c(x[2],x[2]+di,x[2]+di,x[2])
      ys4<-c(x[3],x[3],x[3]+di,x[3]+di)
      zs4<-c(x[4],x[4],x[4],x[4])

      xs5<-c(x[2],x[2]+di,x[2]+di,x[2])
      ys5<-c(x[3],x[3],x[3],x[3])
      zs5<-c(x[4],x[4],x[4]+di,x[4]+di)

      xs6<-c(x[2],x[2],x[2],x[2])
      ys6<-c(x[3],x[3],x[3]+di,x[3]+di)
      zs6<-c(x[4],x[4]+di,x[4]+di,x[4])

      polygon3d(xs1,ys1,zs1,col=cl[i],coords = c(1,3))
      polygon3d(xs2,ys2,zs2,col=cl[i],coords=c(1,2))
      polygon3d(xs3,ys3,zs3,col=cl[i],coords=c(1,2))
      polygon3d(xs4,ys4,zs4,col=cl[i],coords = c(1,2),plot = TRUE)
      polygon3d(xs5,ys5,zs5,col=cl[i],coords = c(1,3),plot = TRUE)
      polygon3d(xs6,ys6,zs6,col=cl[i],coords = c(2,3),plot=TRUE)
    }
  }
  else{
    if(plt==TRUE){
      plot(D[,2],D[,3],type='n',xlim=c(mi,ma),ylim=c(mi,ma),xlab='x2',ylab = 'x3',asp=1)
    }
    for (i in 1:(nrow(D))){
      x<-D[i,]
      xs1<-c(x[2],x[2]-di)
      ys1<-c(x[3],x[3]-di)

      xs2<-c(x[2],x[2]+di)
      ys2<-c(x[3],x[3])

      xs3<-c(x[2],x[2])
      ys3<-c(x[3],x[3]+di)

      lines(xs1,ys1,col=cl[i])
      lines(xs2,ys2,col=cl[i])
      lines(xs3,ys3,col=cl[i])
    }
  }
}
##########Drawing 3D hyperplanes for a given set of vertices ############
## Author :  David Barnhill                                            ##
## Date   :  November 21st 2022                                        ##
## Program:  This code produces the 3D tropical max-plus hyperplanes   ##
##           for a given set of vertices defining a tropical polytope. ##
## Input  :  A matrix, D, of vertices; maximum length, di; minimum     ##
##           value for each coordinate axis, mi; maximum value for each##
##           coordinate axis, ma; logical to determine whether to plot.##
## Output :  Plot of max-plus hyperplane defining a tropical polytope.##
## Execute:  type in R as                                              ##
#########################################################################
hyper3d_max<-function(D,di,mi,ma,plt=FALSE){
  cl<-rainbow(nrow(D))
  d<-dim(D)
  if((d[2]-1)==3){
    if(plt==TRUE){
      plot3d(D[,2],D[,3],D[,4],type='n',xlim=c(mi,ma),ylim=c(mi,ma),zlim=c(mi,ma),xlab='x2',ylab = 'x3',zlab='x4',asp=1)
    }
    for (i in 1:(nrow(D))){
      x<-D[i,]
      xs1<-c(x[2],x[2]+di,x[2]+di,x[2])
      ys1<-c(x[3],x[3]+di,x[3]+di,x[3])
      zs1<-c(x[4],x[4]+di,x[4]-di,x[4]-di)

      xs2<-c(x[2],x[2]+di,x[2]+di,x[2])
      ys2<-c(x[3],x[3]+di,x[3]-di,x[3]-di)
      zs2<-c(x[4],x[4]+di,x[4]+di,x[4])

      xs3<-c(x[2],x[2]+di,x[2]-di,x[2]-di)
      ys3<-c(x[3],x[3]+di,x[3]+di,x[3])
      zs3<-c(x[4],x[4]+di,x[4]+di,x[4])

      xs4<-c(x[2],x[2]-di,x[2]-di,x[2])
      ys4<-c(x[3],x[3],x[3]-di,x[3]-di)
      zs4<-c(x[4],x[4],x[4],x[4])

      xs5<-c(x[2],x[2]-di,x[2]-di,x[2])
      ys5<-c(x[3],x[3],x[3],x[3])
      zs5<-c(x[4],x[4],x[4]-di,x[4]-di)

      xs6<-c(x[2],x[2],x[2],x[2])
      ys6<-c(x[3],x[3],x[3]-di,x[3]-di)
      zs6<-c(x[4],x[4]-di,x[4]-di,x[4])

      polygon3d(xs1,ys1,zs1,coords=c(1,3),col=cl[i])
      polygon3d(xs2,ys2,zs2,col=cl[i],coords = c(2,3))
      polygon3d(xs3,ys3,zs3,col=cl[i],coords=c(1,2))
      polygon3d(xs4,ys4,zs4,col=cl[i],coords = c(1,2),plot = TRUE)
      polygon3d(xs5,ys5,zs5,col=cl[i],coords = c(1,3),plot = TRUE)
      polygon3d(xs6,ys6,zs6,col=cl[i],coords = c(2,3),plot=TRUE)
    }
  }
  else{
    if(plt==TRUE){
      plot(D[,2],D[,3],type='n',xlim=c(mi,ma),ylim=c(mi,ma),xlab='x2',ylab = 'x3',asp=1)
    }
    for (i in 1:(nrow(D))){
      x<-D[i,]
      xs1<-c(x[2],x[2]+di)
      ys1<-c(x[3],x[3]+di)

      xs2<-c(x[2],x[2]-di)
      ys2<-c(x[3],x[3])

      xs3<-c(x[2],x[2])
      ys3<-c(x[3],x[3]-di)

      lines(xs1,ys1,col=cl[i])
      lines(xs2,ys2,col=cl[i])
      lines(xs3,ys3,col=cl[i])
    }
  }
}

############Tropical Determinant of a matrix#############################
## Author :  David Barnhill                                            ##
## Date   :  January 8th 2023                                          ##
## Program:  This code calculates the tropical determinant of a square ##
##           matrix.  It assumes that the matrix is non-singular.      ##
## Input  :  A square matrix, P, of tropical coordinates with the      ##
##           the matrix arranged with the coordinates as row vectors.  ##
## Output(list) :  1) value of the tropical determinant; 2) matrix of  ##
##                 original coordinates reordered by value of          ##
##                 contribution to tropical determinant (small to      ##
##                 large).                                             ##
## Execute:  type in R as                                              ##
#########################################################################
tdet<-function(P){
  dd<-dim(P)
  if(dd[[1]]!=dd[[2]]){
    print("Not a Square Matrix!")
  }
  else{
    PP<-matrix(0,nrow(P),0,TRUE)
    K<-t(P)
    i<-ncol(K)
    tdet<-0
    while (i>1){
      ind<-which.max(K[i,])
      tdet<-tdet+K[i,ind]
      PP<-cbind(K[,ind],PP)
      K<-K[,-ind]
      if(i>1){
        i=i-1
      }
    }

  tdet<-tdet+K[i]
  PP<-cbind(K,PP)%*%diag(1,nrow(PP))
  return(list(tdet,PP))}
}

#### Second Version ####
tdets<-function(P){
  dd<-dim(P)
  B<-P
  if(dd[[1]]!=dd[[2]]){
    return(print("Not a Square Matrix!"))
  }
  else{
    tds<-c(0,0)
    perms<-permn(dd[[1]])
    tdet<-0
    i=1
    max_ind<-0
    while(i<=length(perms)){
      k<-perms[[i]]
      t<-0
      for(j in 1:length(k)){
        t<-t+P[j,k[j]]
      }
      if(t>tdet){
        tdet<-t
        tds<-c(tdet,0)
        max_ind<-perms[[i]]
      }
      else if (t==tdet){
        tds<-c(tdet,t)
      }
      i=i+1
    }
    if(tds[1]==tds[2]){
      return(print('Singular'))
    }
    else{
      for (i in 1:length(max_ind)){
        P[max_ind[i],]<-B[i,]
        }
      return(list(tdet,P))
    }
  }
}


############Rounding Algorithm for a tropical polytope###################
## Author :  David Barnhill                                            ##
## Date   :  January 8th 2023                                          ##
## Program:  This code enumerates the pseudo-vertices of the boundary  ##
##           of a full-dimensional sector of a tropical polytope.      ##
## Input  :  A matrix, V, of vertices defining the tropical convex hull##
##           of a polytope P.                                          ##
## Output :  matrix of pseudo-vertices for the full dimensional part   ##
##           of a tropical polytope.                                   ##
## Execute:  type in R as                                              ##
#########################################################################

rounding<-function(P){
  PP_star<-tdet(P)
  PP<-PP_star[[2]]
  for (i in 1:ncol(PP)){
    PP[,i]<-PP[,i]-PP[i,i]
  }
  b1<-rep(0,(nrow(PP)*(nrow(PP)-1)))
  k<-1
  for (i in 1:nrow(PP)){
    for(j in 1:ncol(PP)){
      if (i!=j){
        b1[k]<-PP[i,j]
        k=k+1}
    }
  }

  B<-matrix(NA,0,ncol(P))
  for (i in 1:nrow(PP)){
    p<-rep(0,ncol(PP))
    for (j in 1:ncol(PP)){
      pt<-p
      if(i==j) next
      if (j!=i){}
      pt[i]=1
      pt[j]=-1
      B<-rbind(B,pt)
    }
  }
  H<-makeH(-B[,-1],-b1)
  V<-scdd(H)
  V1<-cbind(rep(0,nrow(V$output[,c(3:ncol(V$output))])),V$output[,c(3:ncol(V$output))])
  return(V1)
}

#########Minimum Encompassing Ball for a tropical polytope###############
## Author :  David Barnhill                                            ##
## Date   :  January 9th 2023                                          ##
## Program:  This code produces a center point and radius of the       ##
##           minimum encompassing ball for a tropical polytope.        ##
## Input  :  A matrix, A, of vertices defining the tropical convex hull##
##           of a polytope P. Points are rows of matrix A.             ##
## Output :  Center point for a minimum encompassing ball for a        ##
##           tropical polytope, P, and associated radius.              ##
## Execute:  type in R as                                              ##
#########################################################################

min_enc_ball<-function(A){
  P<-permutations(ncol(A),2)
  V<-matrix(0,0,ncol(A))
  bb<-c()
  for (j in 1:nrow(P)){
    for (i in 1:nrow(A)){
      k<-A[i,P[j,1]]-A[i,P[j,2]]
      bb<-append(bb,k)
      a<-rep(0,ncol(A))
      a[P[j,1]]<-1
      a[P[j,2]]<--1
      V<-rbind(V,a)
    }
  }
  r<-rep(-1,nrow(V))
  V<-cbind(V,r)
  f.obj<-c(rep(0,ncol(A)),1)
  f.con<-V
  f.dir <- rep("<=",nrow(V))
  f.rhs<-bb

  res<-lp ("min", f.obj, f.con, f.dir, f.rhs)
  sol<-res$solution
  cent<-sol[1:ncol(A)]
  rad<-sol[length(sol)]
  return(list(cent,rad))
}

#########Maximum Inscribed Ball for a tropical polytope##################
## Author :  David Barnhill                                            ##
## Date   :  January 10th 2023                                         ##
## Program:  This code produces a center point and radius of the       ##
##           maximum inscribed ball for a tropical polytope.           ##
## Input  :  A matrix, A, of vertices defining the tropical convex hull##
##           of a polytope P. Points are rows of matrix A.             ##
## Output :  Center point and radius for a minimum encompassing ball   ##
##           for a tropical polytope, P, and associated radius.        ##
## Execute:  type in R as                                              ##
#########################################################################

max_ins_ball<-function(A){
  n<-rep(0,(ncol(A)))
  A<-tdets(A)[[2]]
  for (i in 2:ncol(A)){
    if(min(A[,i])<0){
      n[i]<-min(A[,i])
      A[,i]<-A[,i]-min(A[,i])
    }
  }
  W<-matrix(0,0,ncol(A))
  P<-permutations((ncol(A)),2)
  bb<-c()
  for(i in 1:nrow(A)){
    A[i,]<-A[i,]-A[i,i]
  }
  A<-t(A)
  for (i in 1:nrow(P)){
    if(P[i,1]==1){
      a<-rep(0,ncol(A))
      a[P[i,2]-1]=1
      a[length(a)]=2
      W<-rbind(W,a)
      bb<-append(bb,A[P[i,1],P[i,2]])
    }
    else if(P[i,2]==1){
      a<-rep(0,ncol(A))
      a[P[i,1]-1]<--1
      W<-rbind(W,a)
      bb<-append(bb,A[P[i,1],P[i,2]])
    }
    else{
      a<-rep(0,ncol(A))
      a[P[i,1]-1]<--1
      a[P[i,2]-1]<-1
      a[length(a)]<-1
      W<-rbind(W,a)
      bb<-append(bb,A[P[i,1],P[i,2]])
    }
  }
  f.con<-W
  f.dir<-c(rep("<=",(ncol(A)^2-ncol(A))))
  f.rhs<--bb
  f.obj<-c(rep(0,(ncol(A)-1)),1)
  sol<-lp ("max", f.obj, f.con, f.dir, f.rhs)
  solu<-sol$solution
  rad<-solu[length(solu)]
  cent<-solu[1:(length(solu)-1)]+n[2:length(n)]+rad
  return(list(rad,c(0,cent)))
}

########## Tropical PCA ##########
###########################################
## Author :  Ruriko Yoshida
## Date   :  April 4th 2022
## Update :  April 13th 2022
## Program:  This code produces a tropical PCA with HAR of ultrametric trees
## Input  :  
## Output :  
## Execute: type in R as 
##
#############################################

library(pracma)

Sum.Residuals <- function(S, D){
  ## S is the set of vertices of a tropical polytope and D is a set of data
  d <- dim(D)
  ## d[1] is the sample size
  y <- 0
  for(i in 1:d[1]){
    y <- y + trop.dist(D[i,], project_pi(S, D[i,]))
  }
  return(y)
}

tropical.PCA <- function(S, D, n, h, I = 1){
  ## I is the number of iterations, n is the number of leaves
  d <- dim(D)
  s <- dim(S)
  ## s[1] is the number of principal components of the tropical PCA
  P <- Sum.Residuals(S, D)
  S.star <- S
  S0 <- S
  for(i in 1:I){
    for(j in 1:s[1]){
      Sp <- S0
      Sp[j, ] <- Ultrametrics.HAR(Sp[j, ], n, 1, h)
      A <- Sum.Residuals(S0, D)/Sum.Residuals(Sp, D)
      if(runif(1)<A){
        S0 <- Sp       # accept move with probabily min(1,A)
      }
      if(Sum.Residuals(S0, D) < Sum.Residuals(S.star, D))
        S.star <- S0
    }
  }
  D1 <- D
  for(i in 1:d[1])
    D1[i, ] <- normaliz.tree(project_pi(S.star, D[i,]), h)
  
  return(list(Sum.Residuals(S.star, D), S.star, D1))
}

tropical.PCA.Polytope <- function(S, D, V, I = 1){
  ## I is the number of iterations, V is a matrix whose row is a vertex of a bigger tropical polytope.
  d <- dim(D)
  s <- dim(S)
  ## s[1] is the number of principal components of the tropical PCA
  P <- Sum.Residuals(S, D)
  S.star <- S
  S0 <- S
  for(i in 1:I){
    for(j in 1:s[1]){
      Sp <- S0
      Sp[j, ] <-TropicalPolytope.HAR(V, Sp[j, ], 1)
      A <- Sum.Residuals(S0, D)/Sum.Residuals(Sp, D)
      if(runif(1)<A){
        S0 <- Sp       # accept move with probabily min(1,A)
      }
      if(Sum.Residuals(S0, D) < Sum.Residuals(S.star, D))
        S.star <- S0
    }
  }
  D1 <- D
  for(i in 1:d[1])
    D1[i, ] <- normaliz.vector(project_pi(S.star, D[i,]))
  
  return(list(Sum.Residuals(S.star, D), S.star, D1))
}


normalize.ultrametrices <- function(D){
  k <- ncol(D)
  new.D <- matrix(rep(0, 2*k), nrow=2, ncol=k)
  for(i in 2:3)
    new.D[i-1, ] <- D[i, ] - D[1, ]
  return(new.D)
}



tropical.geodesic.dim.2 <- function(D1, D2, flag = 0){
  k <- length(D1)
  if(k != 2) warning("dimension has to be 2!")
  for(i in 1:k)
    D1[i] <- round(D1[i], 4)
  for(i in 1:k)
    D2[i] <- round(D2[i], 4)
  if(length(D2) != k)
    warning("dimension is wrong!")
  addd <- 0
  if(flag == 1){
    tmp.D <- D2
    D2 <- D1
    D1 <- tmp.D
  }
  tmp.metric <- (D2 - D1)
  sorted.tmp.metric <- sort.int(tmp.metric, index.return=TRUE)
  ##cat(sorted.tmp.metric$x, "\n")
  D <- rep(0, k)
  
  D[sorted.tmp.metric$ix[2]] <- D2[sorted.tmp.metric$ix[2]]
  D[sorted.tmp.metric$ix[1]] <- min(D2[sorted.tmp.metric$ix[2]] - D1[sorted.tmp.metric$ix[2]] + D1[sorted.tmp.metric$ix[1]], D1[sorted.tmp.metric$ix[1]])
  
  distance <- max(abs(D1 - D))
  distance <- distance + max(abs(D2 - D))
  
  segment <- matrix(rep(0, 6), nrow=2, ncol=3)
  segment[,1] <- D1
  segment[,2] <- D
  segment[,3] <- D2
  
  return(list(segment, distance))
}

polytope_iso <- function(D, P){
  e = length(P)
  s = dim(D)[[1]]
  Q = mat.or.vec(1, s)
  for (i in seq(s)){
    maxvalue = D[i,1] - P[[1]]
    for (j in seq(e)){
      maxvalue = max(maxvalue, D[i,j] - P[[j]])
    }
    Q[[i]]=maxvalue
  }
  return(Q)
}

plot.trop.triangle <- function(D){
  k <- ncol(D)
  pdf("Tropical_Triangle.pdf")
  plot(D[1,],D[2,])
  for(i in 1:(k - 1)){
    for(j in (i + 1):k){
      tseg1 <- tropical.geodesic.dim.2(D[,i],D[,j])
      tseg2 <- tropical.geodesic.dim.2(D[,i],D[,j],flag=1)
      if(tseg1[[2]] < tseg2[[2]]) tseg <- tseg1
      else tseg <- tseg2
      segments(tseg[[1]][1,1],tseg[[1]][2,1],tseg[[1]][1,2],tseg[[1]][2,2],col= 'black')
      segments(tseg[[1]][1,2],tseg[[1]][2,2],tseg[[1]][1,3],tseg[[1]][2,3],col= 'black')
    }
  }
  dev.off()
}

pre.pplot.pro <- function(S, D){
  d <- dim(D)
  s <- dim(S)
  
  DD <- matrix(rep(0, s[1]*d[1]), d[1], s[1])
  for(i in 1:d[1]){
    DD[i, ] <- normaliz.vector(polytope_iso(S, D[i, ]))
  }
  return(DD)
}

plot.trop.triangle.w.points <- function(S, D, file="Tropical_Triangle.pdf"){
  k <- ncol(S)
  s <- dim(S)
  pdf(file)
  plot(S[1,],S[2,])
  for(i in 1:(k - 1)){
    for(j in (i + 1):k){
      tseg1 <- tropical.geodesic.dim.2(S[,i],S[,j])
      tseg2 <- tropical.geodesic.dim.2(S[,i],S[,j],flag=1)
      if(tseg1[[2]] < tseg2[[2]]) tseg <- tseg1
      else tseg <- tseg2
      segments(tseg[[1]][1,1],tseg[[1]][2,1],tseg[[1]][1,2],tseg[[1]][2,2],col= 'black')
      segments(tseg[[1]][1,2],tseg[[1]][2,2],tseg[[1]][1,3],tseg[[1]][2,3],col= 'black')
    }
  }
  
  points(x=D[,2],y=D[,3],pch=16,cex=0.6,col= "red")
  
  dev.off()
  
}


## D is a matrix whose rows are observation and n is the number of leaves, leaves is a set of labels for leaves.
tree.topology.type <- function(D, n, label){
  d <- dim(D)
  
  D0 <-matrix(rep(0, n*n), n, n)
  t <- D[1, ]
  count <- 1
  for(ii in 1:(n-1)){
    for(jj in (ii+1):n){
      D0[ii, jj] <- t[count]
      D0[jj, ii] <- D0[ii, jj]
      count <- count + 1
    }
  }
  tree <- upgma(D0)
  
  sampled.trees.top <- as.multiPhylo(tree)
  sampled.trees.top2 <- rep(0, d[1])
  sampled.trees.top2[1] <- 1
  for(i in 2:d[1]){
    D0 <-matrix(rep(0, n*n), n, n)
    t <- D[i, ]
    count <- 1
    for(ii in 1:(n-1)){
      for(jj in (ii+1):n){
        D0[ii, jj] <- t[count]
        D0[jj, ii] <- D0[ii, jj]
        count <- count + 1
      }
    }
    tree <- upgma(D0)
    N.Trees <- length(sampled.trees.top)
    flag <- 0
    for(j in 1:N.Trees){
      if(all.equal(sampled.trees.top[[j]], tree, use.edge.length = FALSE) == TRUE){
        sampled.trees.top2[i] <- j
        flag <- 1
      }
    }
    if(flag == 0){
      sampled.trees.top <- c(sampled.trees.top, tree)
      sampled.trees.top2[i] <- N.Trees + 1
    }
  }
  
  return(list(sampled.trees.top,  sampled.trees.top2))
}

plot.trop.triangle.w.top <- function(S, D, tree.type, file="Tropical_Triangle_Trees.pdf"){
  k <- ncol(S)
  s <- dim(S)
  m <- max(tree.type)
  
  pdf(file)
  plot(S[1,],S[2,])
  for(i in 1:(k - 1)){
    for(j in (i + 1):k){
      tseg1 <- tropical.geodesic.dim.2(S[,i],S[,j])
      tseg2 <- tropical.geodesic.dim.2(S[,i],S[,j],flag=1)
      if(tseg1[[2]] < tseg2[[2]]) tseg <- tseg1
      else tseg <- tseg2
      segments(tseg[[1]][1,1],tseg[[1]][2,1],tseg[[1]][1,2],tseg[[1]][2,2],col= 'black')
      segments(tseg[[1]][1,2],tseg[[1]][2,2],tseg[[1]][1,3],tseg[[1]][2,3],col= 'black')
    }
  }
  L <- rep(0, m)
  index <- list()
  
  for(i in 1:m){
    L[i] <- length(which(tree.type == i))
    index[[i]] <- which(tree.type == i)
  }
  co <- rainbow(m)
  for(i in 1:m){
    points(x=D[index[[rev(order(L))[i]]], 2],y=D[index[[rev(order(L))[i]]], 3],pch=16,cex=0.6,col= co[i])
  }
  dev.off()
  
  return(L)
  
}

plot.tree.PCA <- function(tree.list, freq, file="Tree_Topology.pdf"){
  T <- length(tree.list)
  co <- rainbow(T)
  pdf(file)
  s <- sum(freq)
  par(mfrow=c(round(T/2),2))
  for(i in 1:T){
    w <- printf("Tree topology (%d)", freq[rev(order(freq))[i]]) 
    plot(tree.list[[rev(order(freq))[i]]])
    legend(0, 8, legend=c(w),
           col=c(co[i]), lty=1:2, cex=0.8)
  }
  dev.off()    
  
}
########### Tropical SVM #############
T.SVM<-function(V,clses,L=1000,tst=.8,st=100){
  specs<-as.vector(unique(clses))
  dt<-sample(nrow(V),tst*nrow(V))
  V_tr<-V[dt,]
  V_test<-V[-dt,-ncol(V)]
  V_cl<-V[-dt,ncol(V)]
  
  yy<-V_tr[,ncol(V_tr)]
  xx<-V_tr[,1:(ncol(V_tr)-1)]
  
  v<-apply(xx,2,min)
  max_v<-apply(xx,2,max)
  cc<-matrix(0,0,ncol(xx),TRUE)
  cc<-rbind(cc,v)
  for (i in 2:length(max_v)){
    v1<-v
    v1[i]<-max_v[i]
    cc<-rbind(cc,v1)
  }
  
  #B_P<-min_enc_ball(xx)
  
  #B_r<-trop_bal.vert(B_P[[1]],B_P[[2]],ncol(xx))
  
  # Starting values
  x0<-apply(xx,2,mean)
  #x0<-B_P[[1]] # initial point
  w_star<--x0 # normal vector of initial point
  
  ## This tells me which sector each point is in relative to the new
  Tstar<-apply(xx,1,function(x) which.max(x+w_star))
  
  gin<-cbind(yy,Tstar)
  c0<-matrix(rep(0,ncol(xx)*length(specs)),ncol(xx),length(specs),TRUE)
  for (j in 1:nrow(gin)){
    sp<-gin[j,1]
    sec<-gin[j,2]
    c0[sec,sp]<-c0[sec,sp]+1
  }
  
  rc0<-rowSums(c0)
  c1<-c0
  for (i in 1:nrow(c0)){
    if(rc0[i]>0){
      c1[i,]<-c0[i,]/rc0[i]*(1-c0[i,]/rc0[i])
    }
    else{
      c1[i,]<-0
    }
  }
  g<-rowSums(c1)
  rc1<-rc0/nrow(xx)
  gini_star<-g%*%rc1
  
  teaky<-cbind(xx,Tstar)
  co<-0
  i=1
  for (i in 1:ncol(xx)){
    teaks<-matrix(teaky[teaky[,ncol(teaky)]==i,],ncol=ncol(teaky))
    if(nrow(teaks)>0){
      max_min_dis<-apply(matrix(teaks[,-ncol(teaks)],ncol=ncol(teaks)-1),1,function(x) trop.dist.hyp_max(w_star,x))
      ma_mi_dis<-min(max_min_dis)
      co<-co+ma_mi_dis
    }
  }
  c_star<-co*(gini_star-1)
  
  ##### loop
  
  N<-L # number of points
  har_norms1<-matrix(0,N,ncol(xx)+1,TRUE) # matrix to capture the walk
  k<-1
  costs=1
  sto<-st
  while(k<=N){
    print(k)
    if(costs<sto){
      T<-1-k/(1.2*N)
      y<-TropicalPolytope.extrapolation.HAR_v4(cc,x0,I=50,(ncol(xx)-1)) # choose a point for the next normal vector
      w<--y # convert to normal vector
      # From here we find the sectors
      Tx<-apply(xx,1,function(x) which.max(x+w))
      gin<-cbind(yy,Tx)
      c0<-matrix(rep(0,ncol(xx)*length(specs)),ncol(xx),length(specs),TRUE)
      for (j in 1:nrow(gin)){
        sp<-gin[j,1]
        sec<-gin[j,2]
        c0[sec,sp]<-c0[sec,sp]+1
      }
      rc0<-rowSums(c0)
      c1<-c0
      for (i in 1:nrow(c0)){
        if(rc0[i]>0){
          c1[i,]<-c0[i,]/rc0[i]*(1-c0[i,]/rc0[i])
        }
        else{
          c1[i,]<-0
        }
      }
      g<-rowSums(c1)
      rc1<-rc0/nrow(xx)
      gini_prop<-g%*%rc1
      teaky<-cbind(xx,Tstar)
      co<-0
      for (i in 1:ncol(xx)){
        teaks<-matrix(teaky[teaky[,ncol(teaky)]==i,],ncol=ncol(teaky))
        if(nrow(teaks)>0){
          max_min_dis<-min(apply(matrix(teaks[,-ncol(teaks)],ncol=ncol(teaks)-1),1,function(x) trop.dist.hyp_max(w_star,x)))
          ma_mi_dis<-min(max_min_dis)
          co<-co+ma_mi_dis
        }
      }
      c_prop<-co*(gini_prop-1)
      ## MH from here
      A<-exp(-(c_prop/T))/exp(-(c_star/T))
      p<-runif(1,0,1)
      if(p<A){
        har_norms1[k,1:(ncol(har_norms1)-1)]<-y
        har_norms1[k,ncol(har_norms1)]<-c_prop
        x0<-y
        c_star<-c_prop
        k<-k+1
        costs<-1
      }
      else{
        costs<-costs+1
      }
    }
    else{
      break
    }
  }
  
  ind<-which.min(har_norms1[1:(k-1),ncol(har_norms1)])
  ind2<-max(which(har_norms1[,ncol(har_norms1)]==har_norms1[ind,ncol(har_norms1)]))
  min_vec<-har_norms1[ind2,1:(ncol(har_norms1)-1)]
  w_star<--min_vec # normal vector of initial point
  ## This tells me which sector each point is in relative to the new
  Tstar<-apply(V_test,1,function(x) which.max(x+w_star))
  gin<-cbind(V_cl,Tstar)
  cc0<-matrix(rep(0,ncol(V_test)*length(specs)),ncol(V_test),length(specs),TRUE)
  for (j in 1:nrow(gin)){
    sp<-gin[j,1]
    sec<-gin[j,2]
    cc0[sec,sp]<-cc0[sec,sp]+1
  }
  
  max_inds<-apply(cc0,1,function(x) which.max(x))
  maxes<-apply(cc0,1,function(x) max(x))
  ma<-cbind(maxes,max_inds)
  conf_mat<-matrix(0,length(specs),length(specs))
  for (i in 1:nrow(ma)){
    conf_mat[ma[i,2],ma[i,2]]<-conf_mat[ma[i,2],ma[i,2]]+ma[i,1]
  }
  corr_prob<-sum(conf_mat)/nrow(V_test)
  pres<-list(conf_mat,corr_prob)
  return(pres)
}

########## KDE ###########

trop.zero <- -1000000

kernel.ultrametric <- function(x, mu, s){
  return(exp(-(trop.dist(mu, x)/s)))
}

### bw.nn function: Using Grady's code from KDETree package
bw.nn <- function(x,prop=0.2,tol=1e-6){
  #  out <- apply(x,1,function(y) quantile(y,prop))
  out <- apply(x, 1, quantile, prop)
  is.zero <- out < tol
  if(sum(is.zero)>0)
    out[is.zero] <- apply(x[is.zero,],1,function(y) min(y[y>tol]))
  out
}
#####

pw.trop.dist <- function(D1, D2){
  d1 <- dim(D1)
  d2 <- dim(D2)
  D <- matrix(rep(100000, d1[1]*d2[1]), d1[1], d2[1])
  for(i in 1:d1[1])
    for(j in 1:d2[1])
      D[i, j] <- trop.dist(D1[i, ], D2[j, ])
  return(D)    
}


tropical.KDE <- function(D, n, sigma, h = 2){
  ## D is a data set.  each row is an obs.
  ## n is the number of leaves
  ## h is a heigth.
  d <- dim(D)
  P <- rep(0, d[1]) ## estimated probability
  for(i in 1:d[1]){
    D[i, ] <- normaliz.tree(D[i, ], h)
    for(j in 1:d[1]){
      if(i != j)
        P[i] <- P[i] + kernel.ultrametric(D[i, ], D[j, ], sigma[j])
    }
    P[i] <- P[i]/(d[1] - 1)
  }
  return(P)
}


