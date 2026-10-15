-- Prove2me | Theorems.Thm_OAI_ParityWL_BalancedStar_representatives
-- name    : OAI.ParityWL.BalancedStar.representatives
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:41:12.574095+00:00
-- url     : https://prove2.me/theorems/44f34b4e-e1c0-40a5-8254-b819ed358bd3
-- title:
--   The bag of a balanced star contains exactly one vertex of each main type
-- statement:
--   Let $t\in\mathbb{N}$. The *template graph* $T_t$ has vertex set $[t]\sqcup\mathcal{H}_t$, where $[t]=\{0,1,\dots,t-1\}$ is the set of *main vertices* and $\mathcal{H}_t$ is the set of *helper vertices* $h=(i,j;m)$ with $i<j$ in $[t]$ and $m\in[t]\setminus\{i,j\}$. Any two distinct main vertices are adjacent, each helper $(i,j;m)$ is adjacent exactly to the three main vertices $i$, $j$ and $m$, and no two helpers are adjacent. The *star parity* $\beta_t\colon[t]\sqcup\mathcal{H}_t\to\mathbb{F}_2$ takes the value $1$ at the main vertex $0$ and the value $0$ at every other template vertex. Let $F$ be a graph on a finite set $W$ and let $a\colon F\to T_t$ be a graph homomorphism; $a(x)$ is the *type* of $x\in W$, and a vertex of main type $i$ means a vertex $x$ with $a(x)=i$.
--
--   A *weighted witness* $w=(\lambda,\mu)$ for $(T_t,F,a,\beta_t)$ consists of vertex weights $\lambda\colon W\to\mathbb{F}_2$ and edge weights $\mu\colon W\times W\to\mathbb{F}_2$ such that $\mu(x,y)=\mu(y,x)$, $\mu(x,y)=0$ whenever $xy$ is not an edge of $F$, $\sum_{y\in W,\ a(y)=u}\mu(x,y)=\lambda(x)$ for every $x\in W$ and every neighbour $u$ of $a(x)$ in $T_t$, and $\sum_{x\in W}\lambda(x)\,\beta_t(a(x))=1$. For $Y\subseteq W$ and a template vertex $u$, the *mass* of type $u$ on $Y$ is $m_Y(u)=\sum_{x\in Y,\ a(x)=u}\lambda(x)$.
--
--   A *balanced star* for $w$ consists of a number $n$ of regions, a map $\rho\colon W\to\{\ast\}\sqcup\{0,\dots,n-1\}$ whose fibre $B=\rho^{-1}(\ast)$, the *bag*, has $|B|\le t$, and for each region $r<n$ a *separator* $S_r\subseteq B$ with $|S_r|<t$, such that, writing $Y_r=\rho^{-1}(r)$ for the $r$-th region: (i) every edge of $F$ from a vertex of $Y_r$ to a vertex outside $Y_r$ ends in $S_r$; (ii) for every main index $j\in[t]$ such that no vertex of $S_r$ has type $j$, the mass vanishes: $m_{Y_r}(j)=0$.
--
--   **Theorem.** Let $t>0$, let $w$ be a weighted witness for $(T_t,F,a,\beta_t)$, and let $s$ be a balanced star for $w$ with bag $B$. Then there is a map $x\colon[t]\to W$ such that
--   $$
--   a(x_i)=i\quad\text{for every } i\in[t]\qquad\text{and}\qquad B=\{x_0,x_1,\dots,x_{t-1}\}.
--   $$
--
--   Consequently the bag has exactly $t$ elements, one of each main type, and contains no vertex of helper type. This identifies the central bag of a balanced star with a system of representatives of the main template vertices; when $a$ factors through the base graph of a choice system, these representatives supply the candidate solution of the choice system.
--
--   **Formalization Note** `WeightedWitness T F a b` has fields `vertex` ($\lambda$), `edge` ($\mu$), `symmetric`, `supported`, `coordinate` and `odd`; `Bit` is `ZMod 2`. `BalancedStar w` is a structure with fields `regions`, `region` (the map $\rho$, with values in `Option (Fin regions)` and `none` playing the role of $\ast$), `bag`, `separator` and the listed properties; the mass is `w.mass Y u`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/BalancedBags.lean#L88-L105

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
variable {t : ℕ} {W : Type} [Fintype W] {F : SimpleGraph W}
variable {a : F →g template t} {b : TemplateVertex t → Bit}

theorem OAI.ParityWL.BalancedStar.representatives (w : WeightedWitness (template t) F a (starParity t))
    (s : BalancedStar w) (ht : 0 < t) :
    ∃ x : Fin t → W, (∀ i, a (x i) = .inl i) ∧
      s.bag = Finset.univ.image x := by sorry
