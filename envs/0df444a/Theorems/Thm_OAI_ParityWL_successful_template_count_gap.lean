-- Prove2me | Theorems.Thm_OAI_ParityWL_successful_template_count_gap
-- name    : OAI.ParityWL.successful_template_count_gap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:43:20.793569+00:00
-- url     : https://prove2.me/theorems/b885f1df-1cb2-45aa-a659-4eab78078f0c
-- title:
--   A successful choice system gives strictly fewer template homomorphisms into the star lift
-- statement:
--   Let $t\in\mathbb{N}$. A *choice system* $C$ on $t$ consists of a finite domain $D_i$ for each $i\in[t]$, a finite label set $L_{ij}$ for each pair $i<j$ in $[t]$, and label maps $\ell_{ij}\colon D_i\to L_{ij}$ (left) and $r_{ij}\colon D_j\to L_{ij}$ (right). It is *successful* if there are $d_i\in D_i$ $(i\in[t])$ with $\ell_{ij}(d_i)=r_{ij}(d_j)$ for all $i<j$.
--
--   The *template graph* $T_t$ has vertex set $[t]\sqcup\mathcal{H}_t$, where $[t]=\{0,1,\dots,t-1\}$ is the set of *main vertices* and $\mathcal{H}_t$ is the set of *helper vertices* $h=(i,j;m)$ with $i<j$ in $[t]$ and $m\in[t]\setminus\{i,j\}$. Any two distinct main vertices are adjacent, each helper $(i,j;m)$ is adjacent exactly to the three main vertices $i$, $j$ and $m$, and no two helpers are adjacent. The *star parity* $\beta_t\colon[t]\sqcup\mathcal{H}_t\to\mathbb{F}_2$ takes the value $1$ at the main vertex $0$ and the value $0$ at every other template vertex.
--
--   The *base graph* $G_C$ has the main base vertices $(i,d)$ with $i\in[t]$, $d\in D_i$, and the helper base vertices $(h,q)$ with $h=(i,j;m)\in\mathcal{H}_t$ and $q\in L_{ij}$. Its edges are: $(i,d)\sim(j,e)$ whenever $i<j$ and $\ell_{ij}(d)=r_{ij}(e)$; and, for every helper $h=(i,j;m)$, the edges $(h,\ell_{ij}(d))\sim(i,d)$, $(h,r_{ij}(e))\sim(j,e)$ and $(h,q)\sim(m,f)$ for all $d\in D_i$, $e\in D_j$, $q\in L_{ij}$, $f\in D_m$. The type map $\pi\colon G_C\to T_t$, $(i,d)\mapsto i$, $(h,q)\mapsto h$, is a graph homomorphism.
--
--   For a graph homomorphism $\tau\colon G\to T$ into a graph $T$ on a finite set $A$ and a parity function $b\colon A\to\mathbb{F}_2$, the *parity lift* $G^{b}$ has as vertices the pairs $(v,z)$ with $v\in V(G)$ and $z\colon N_T(\tau(v))\to\mathbb{F}_2$ a bit assignment on the neighbourhood of $\tau(v)$ in $T$ with $\sum_{u}z(u)=b(\tau(v))$; two vertices $(v,z)$ and $(v',z')$ are adjacent iff $vv'\in E(G)$ and $z(\tau(v'))=z'(\tau(v))$. The *zero lift* $Z_C=G_C^{0}$ and the *star lift* $S_C=G_C^{\beta_t}$ are the lifts of the base graph along $\tau=\pi$ for $b\equiv0$ and $b=\beta_t$. For finite graphs $F$ and $H$, $\hom(F,H)$ denotes the number of graph homomorphisms $F\to H$.
--
--   **Theorem.** If $t>0$ and $C$ is successful, then
--   $$
--   \hom(T_t,S_C)<\hom(T_t,Z_C).
--   $$
--
--   Thus the template graph itself is a pattern whose homomorphism counts distinguish the zero lift from the star lift as soon as the choice system has a solution. Since homomorphism counts from $T_t$ are determined by low-round Weisfeiler–Leman colour histograms, this strict gap is what makes successful choice systems detectable.
--
--   **Formalization Note** `homCount F H` is the cardinality of the type `F →g H` of graph homomorphisms; `zeroLift C` and `starLift C` are `liftGraph` of `baseGraph C` along `baseProjection C` for the parities `fun _ => 0` and `starParity t`. Tags live in `ZMod 2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/Witnesses.lean#L162-L181

import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
import Definitions.Def_OAI_Combinatorics_ParityLifts_Witnesses

open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical
variable {t : ℕ} {C : ChoiceSystem t}

theorem OAI.ParityWL.successful_template_count_gap (ht : 0 < t) (hs : C.Successful) :
    homCount (template t) (starLift C) < homCount (template t) (zeroLift C) := by sorry
