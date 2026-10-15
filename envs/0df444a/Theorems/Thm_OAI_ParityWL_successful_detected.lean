-- Prove2me | Theorems.Thm_OAI_ParityWL_successful_detected
-- name    : OAI.ParityWL.successful_detected
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:45:30.188799+00:00
-- url     : https://prove2.me/theorems/1cd0f887-4c89-49a3-a593-ac2274b0ba08
-- title:
--   Successful choice systems are detected by Weisfeiler–Leman histograms at round $2$ for the joint and round $1$ for the separate convention
-- statement:
--   Let $k\ge4$ and let $c$ be one of the two conventions *joint* or *separate*. Put $t=k+1$ and $r_c=2$ if $c$ is joint, and $t=k$ and $r_c=1$ if $c$ is separate.
--
--   A *choice system* $C$ on $t$ consists of a finite domain $D_i$ for each $i\in[t]$, a finite label set $L_{ij}$ for each pair $i<j$ in $[t]$, and label maps $\ell_{ij}\colon D_i\to L_{ij}$ (left) and $r_{ij}\colon D_j\to L_{ij}$ (right). It is *successful* if there are $d_i\in D_i$ $(i\in[t])$ with $\ell_{ij}(d_i)=r_{ij}(d_j)$ for all $i<j$. The *template graph* $T_t$ has vertex set $[t]\sqcup\mathcal{H}_t$, where $[t]=\{0,1,\dots,t-1\}$ is the set of *main vertices* and $\mathcal{H}_t$ is the set of *helper vertices* $h=(i,j;m)$ with $i<j$ in $[t]$ and $m\in[t]\setminus\{i,j\}$. Any two distinct main vertices are adjacent, each helper $(i,j;m)$ is adjacent exactly to the three main vertices $i$, $j$ and $m$, and no two helpers are adjacent. The *star parity* $\beta_t\colon[t]\sqcup\mathcal{H}_t\to\mathbb{F}_2$ takes the value $1$ at the main vertex $0$ and the value $0$ at every other template vertex.
--
--   The *base graph* $G_C$ has the main base vertices $(i,d)$ with $i\in[t]$, $d\in D_i$, and the helper base vertices $(h,q)$ with $h=(i,j;m)\in\mathcal{H}_t$ and $q\in L_{ij}$. Its edges are: $(i,d)\sim(j,e)$ whenever $i<j$ and $\ell_{ij}(d)=r_{ij}(e)$; and, for every helper $h=(i,j;m)$, the edges $(h,\ell_{ij}(d))\sim(i,d)$, $(h,r_{ij}(e))\sim(j,e)$ and $(h,q)\sim(m,f)$ for all $d\in D_i$, $e\in D_j$, $q\in L_{ij}$, $f\in D_m$. The type map $\pi\colon G_C\to T_t$, $(i,d)\mapsto i$, $(h,q)\mapsto h$, is a graph homomorphism. For a graph homomorphism $\tau\colon G\to T$ into a graph $T$ on a finite set $A$ and a parity function $b\colon A\to\mathbb{F}_2$, the *parity lift* $G^{b}$ has as vertices the pairs $(v,z)$ with $v\in V(G)$ and $z\colon N_T(\tau(v))\to\mathbb{F}_2$ a bit assignment on the neighbourhood of $\tau(v)$ in $T$ with $\sum_{u}z(u)=b(\tau(v))$; two vertices $(v,z)$ and $(v',z')$ are adjacent iff $vv'\in E(G)$ and $z(\tau(v'))=z'(\tau(v))$. The *zero lift* $Z_C=G_C^{0}$ and the *star lift* $S_C=G_C^{\beta_t}$ are the lifts of the base graph along $\tau=\pi$ for $b\equiv0$ and $b=\beta_t$.
--
--   For a finite graph $G$ and a tuple $x\in V(G)^k$, the round-$0$ colour of $x$ is its *atomic type* $\mathrm{atp}_G(x)=\big([x_i=x_j],\,[x_ix_j\in E(G)]\big)_{i,j\in[k]}$, a $k\times k$ array of pairs of truth values. Write $x[i\leftarrow v]$ for $x$ with its $i$-th entry replaced by $v$, and $\{\!\{\cdot\}\!\}$ for multisets. The *joint* colours are
--   $$
--   \chi^{\mathrm J}_{r+1}(x)=\Big(\chi^{\mathrm J}_r(x),\ \big\{\!\big\{\big(\chi^{\mathrm J}_r(x[i\leftarrow v])\big)_{i\in[k]}: v\in V(G)\big\}\!\big\}\Big),
--   $$
--   and the *separate* colours are $\chi^{\mathrm S}_{r+1}(x)=\big(\chi^{\mathrm S}_r(x),\ (\{\!\{\chi^{\mathrm S}_r(x[i\leftarrow v]): v\in V(G)\}\!\})_{i\in[k]}\big)$, both starting from $\chi_0=\mathrm{atp}$. For a convention $c$ and finite graphs $G,H$, the round-$r$ *histograms agree*, written $\mathrm{Hist}^c_{k,r}(G)=\mathrm{Hist}^c_{k,r}(H)$, if the multisets $\{\!\{\chi^c_r(x):x\in V(G)^k\}\!\}$ and $\{\!\{\chi^c_r(y):y\in V(H)^k\}\!\}$ are equal; the round-$r$ *pure histograms agree*, written $\mathrm{PureHist}^c_{k,r}(G)=\mathrm{PureHist}^c_{k,r}(H)$, if the same holds when the colours are computed in the disjoint union $G\sqcup H$ and one compares the tuples lying entirely in $G$ with those lying entirely in $H$.
--
--   **Theorem.** If $C$ is a successful choice system on $t$, then the zero lift and the star lift are distinguished at round $r_c$, both in the ordinary and in the pure sense:
--   $$
--   \mathrm{Hist}^c_{k,r_c}(Z_C)\neq\mathrm{Hist}^c_{k,r_c}(S_C)\qquad\text{and}\qquad\mathrm{PureHist}^c_{k,r_c}(Z_C)\neq\mathrm{PureHist}^c_{k,r_c}(S_C).
--   $$
--
--   This is the detection direction of the parity-lift reduction, including the explicit detection round. As an immediate consequence, if the zero and star lifts are $k$-variable Weisfeiler–Leman equivalent under convention $c$ (histograms agree at every round), in either the ordinary or the pure sense, then $C$ is not successful.
--
--   **Formalization Note** `bagParameter c k` is $t$, `detectionRound c` is $r_c$, and the two claims are the negations of `sameHistogram (zeroLift C) (starLift C) c k (detectionRound c)` and of the corresponding `samePureHistogram`. Colours are `jointColor` and `separateColor`; histograms are multisets `Finset.univ.val.map` over all functions `Fin k → V`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/Detection.lean#L348-L366

import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
import Definitions.Def_OAI_Combinatorics_ParityLifts_Witnesses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BagTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_TagSizes
import Definitions.Def_OAI_Combinatorics_ParityLifts_Detection

open OAI OAI.ParityWL
open scoped BigOperators

theorem OAI.ParityWL.successful_detected (k : ℕ) (hk : 4 ≤ k) (c : Convention)
    (C : ChoiceSystem (bagParameter c k)) (hs : C.Successful) :
    ¬ sameHistogram (zeroLift C) (starLift C) c k (detectionRound c) ∧
    ¬ samePureHistogram (zeroLift C) (starLift C) c k (detectionRound c) := by sorry
