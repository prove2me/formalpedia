-- Prove2me | Theorems.Thm_OAI_ParityWL_choice_of_balancedStar
-- name    : OAI.ParityWL.choice_of_balancedStar
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:41:35.934028+00:00
-- url     : https://prove2.me/theorems/048c8fcf-790a-4dfc-bf61-83e2df56c0ce
-- title:
--   A balanced star for a pulled-back star-parity witness forces a successful choice
-- statement:
--   Let $t\in\mathbb{N}$. A *choice system* $C$ on $t$ consists of a finite domain $D_i$ for each $i\in[t]$, a finite label set $L_{ij}$ for each pair $i<j$ in $[t]$, and label maps $\ell_{ij}\colon D_i\to L_{ij}$ (left) and $r_{ij}\colon D_j\to L_{ij}$ (right). It is *successful* if there are $d_i\in D_i$ $(i\in[t])$ with $\ell_{ij}(d_i)=r_{ij}(d_j)$ for all $i<j$.
--
--   The *template graph* $T_t$ has vertex set $[t]\sqcup\mathcal{H}_t$, where $[t]=\{0,1,\dots,t-1\}$ is the set of *main vertices* and $\mathcal{H}_t$ is the set of *helper vertices* $h=(i,j;m)$ with $i<j$ in $[t]$ and $m\in[t]\setminus\{i,j\}$. Any two distinct main vertices are adjacent, each helper $(i,j;m)$ is adjacent exactly to the three main vertices $i$, $j$ and $m$, and no two helpers are adjacent. The *star parity* $\beta_t\colon[t]\sqcup\mathcal{H}_t\to\mathbb{F}_2$ takes the value $1$ at the main vertex $0$ and the value $0$ at every other template vertex.
--
--   The *base graph* $G_C$ has the main base vertices $(i,d)$ with $i\in[t]$, $d\in D_i$, and the helper base vertices $(h,q)$ with $h=(i,j;m)\in\mathcal{H}_t$ and $q\in L_{ij}$. Its edges are: $(i,d)\sim(j,e)$ whenever $i<j$ and $\ell_{ij}(d)=r_{ij}(e)$; and, for every helper $h=(i,j;m)$, the edges $(h,\ell_{ij}(d))\sim(i,d)$, $(h,r_{ij}(e))\sim(j,e)$ and $(h,q)\sim(m,f)$ for all $d\in D_i$, $e\in D_j$, $q\in L_{ij}$, $f\in D_m$. The type map $\pi\colon G_C\to T_t$, $(i,d)\mapsto i$, $(h,q)\mapsto h$, is a graph homomorphism.
--
--   Let $F$ be a graph on a finite set $W$, let $\varphi\colon F\to G_C$ be a graph homomorphism, and put $a=\pi\circ\varphi\colon F\to T_t$; $a(x)$ is the *type* of $x\in W$. A *weighted witness* $w=(\lambda,\mu)$ for $(T_t,F,a,\beta_t)$ consists of vertex weights $\lambda\colon W\to\mathbb{F}_2$ and edge weights $\mu\colon W\times W\to\mathbb{F}_2$ such that $\mu(x,y)=\mu(y,x)$, $\mu(x,y)=0$ whenever $xy$ is not an edge of $F$, $\sum_{y\in W,\ a(y)=u}\mu(x,y)=\lambda(x)$ for every $x\in W$ and every neighbour $u$ of $a(x)$ in $T_t$, and $\sum_{x\in W}\lambda(x)\,\beta_t(a(x))=1$. For $Y\subseteq W$ and a template vertex $u$, the *mass* of type $u$ on $Y$ is $m_Y(u)=\sum_{x\in Y,\ a(x)=u}\lambda(x)$.
--
--   A *balanced star* for $w$ consists of a number $n$ of regions, a map $\rho\colon W\to\{\ast\}\sqcup\{0,\dots,n-1\}$ whose fibre $B=\rho^{-1}(\ast)$, the *bag*, has $|B|\le t$, and for each region $r<n$ a *separator* $S_r\subseteq B$ with $|S_r|<t$, such that, writing $Y_r=\rho^{-1}(r)$ for the $r$-th region: (i) every edge of $F$ from a vertex of $Y_r$ to a vertex outside $Y_r$ ends in $S_r$; (ii) for every main index $j\in[t]$ such that no vertex of $S_r$ has type $j$, the mass vanishes: $m_{Y_r}(j)=0$.
--
--   **Theorem.** If $t>0$ and there exists a balanced star for a weighted witness $w$ for $(T_t,F,\pi\circ\varphi,\beta_t)$, then $C$ is successful:
--   $$
--   \exists\,(d_i)_{i\in[t]}\in\prod_{i\in[t]}D_i\quad\text{such that}\quad \ell_{ij}(d_i)=r_{ij}(d_j)\ \text{ for all } i<j.
--   $$
--
--   This is the choice-extraction step of the reduction: a parity certificate for the star lift, pulled back along a homomorphism $\varphi$ from a graph $F$ that admits a balanced star, produces a solution of the choice system. Contrapositively, if $C$ is not successful, no such witness exists for any such $F$ and $\varphi$.
--
--   **Formalization Note** `WeightedWitness T F a b` has fields `vertex` ($\lambda$), `edge` ($\mu$), `symmetric`, `supported`, `coordinate` and `odd`; `Bit` is `ZMod 2`. The base graph is `baseGraph C`, the projection is `baseProjection C`, and the witness is over the composite `(baseProjection C).comp φ`. `BalancedStar w` is the structure with fields `regions`, `region`, `bag`, `separator` and the listed properties; `C.Successful` is the existence of a compatible choice.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/ChoiceExtraction.lean#L67-L118

import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags

open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical
variable {t : ℕ} (C : ChoiceSystem t) {W : Type} [Fintype W]
variable {F : SimpleGraph W} (φ : F →g baseGraph C)
variable (w : WeightedWitness (template t) F ((baseProjection C).comp φ) (starParity t))

theorem OAI.ParityWL.choice_of_balancedStar (s : BalancedStar w) (ht : 0 < t) : C.Successful := by sorry
