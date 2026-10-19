-- Prove2me | Theorems.Thm_OAI_Barnette_Network_ColoredDual_remainder_black_degree
-- name    : OAI.Barnette.Network.ColoredDual.remainder_black_degree
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:52:03.808489+00:00
-- url     : https://prove2.me/theorems/bf947b90-6ba2-4349-a563-0dc281535aef
-- title:
--   Black degrees after deleting the removed edge set of a partner pair
-- statement:
--   Let $N$ and $D$ be oriented networks on a common finite edge set $E$, with a finite vertex set $V$ for $N$ and a vertex set $F$ for $D$: every $e\in E$ has a tail $\operatorname{tail}(e)$ and a head $\operatorname{head}(e)$ in $V$, and a tail $\operatorname{tail}_D(e)$ and a head $\operatorname{head}_D(e)$ in $F$. The underlying simple graph of a network joins two distinct vertices when some edge has exactly these two endpoints. For $v\in V$ let $\operatorname{star}(v)\subseteq E$ be the set of edges with tail or head $v$ in $N$. Let $\nabla_N:\mathbb{R}^V\to\mathbb{R}^E$, $(\nabla_N f)(e)=f(\operatorname{head}(e))-f(\operatorname{tail}(e))$, be the gradient and $\partial_N:\mathbb{R}^E\to\mathbb{R}^V$, $(\partial_N x)(v)=\sum_{\operatorname{head}(e)=v}x_e-\sum_{\operatorname{tail}(e)=v}x_e$, the boundary map; $\nabla_D$ and $\partial_D$ are defined in the same way.
--
--   A *colored dual structure* on $(N,D)$ consists of the following data and axioms.
--
--   1. Duality: the underlying simple graphs of $N$ and $D$ are connected, $\ker\partial_N=\operatorname{im}\nabla_D$ and $\ker\partial_D=\operatorname{im}\nabla_N$.
--   2. $N$ and $D$ are simple (no edge has equal tail and head, and distinct edges have distinct unordered pairs of endpoints), and $N$ is cubic: every vertex has exactly three neighbours.
--   3. A set of *black* vertices of $N$ such that every edge has exactly one black endpoint; the other vertices are *white*.
--   4. For every $v\in V$, a triangle of $D$ on $\operatorname{star}(v)$: distinct corners $c^v_0,c^v_1,c^v_2\in F$ and an enumeration $\operatorname{star}(v)=\{\varepsilon^v_0,\varepsilon^v_1,\varepsilon^v_2\}$ by distinct edges such that $\varepsilon^v_k$ joins $c^v_k$ and $c^v_{k+1}$ in $D$ (indices in $\mathbb{Z}/3$), with compatible orientations: $\operatorname{head}(\varepsilon^v_k)=v$ exactly when $\operatorname{tail}_D(\varepsilon^v_k)=c^v_k$.
--
--   Fix a black vertex $r$, the *root*. Let $B_r$ be the set of black vertices different from $r$ and $X_r=F\setminus\{c^r_0,c^r_1,c^r_2\}$. A *state* is a map $s:B_r\to\mathbb{Z}/3$ such that $t\mapsto c^t_{s(t)}$ is a bijection from $B_r$ onto $X_r$: each black vertex other than the root selects a corner of its triangle, and every element of $F$ outside the root triangle is selected exactly once. Two states $\ell,\rho$ are *partners* if $c^t_{\ell(t)}\neq c^t_{\rho(t)}$, equivalently $\ell(t)\neq\rho(t)$, for every $t\in B_r$; a *pair* is an ordered pair $(\ell,\rho)$ of partner states.
--
--   Fix a pair $P=(\ell,\rho)$ and an index $i\in\mathbb{Z}/3$. For $t\in B_r$ let $\tau(t)\in\mathbb{Z}/3$ be the third index, different from $\ell(t)$ and $\rho(t)$. For a vertex $v$ and indices $a\neq b$, let $\sigma^v(a,b)\in\operatorname{star}(v)$ be the edge of the triangle at $v$ joining $c^v_a$ and $c^v_b$; it equals $\varepsilon^v_a$ if $b=a+1$ and $\varepsilon^v_b$ if $a=b+1$. The *label* of $t\in B_r$ and the *removed set* are
--
--   $$q_P(t)=\sigma^t\bigl(\ell(t),\tau(t)\bigr),\qquad R_i(P)=\{q_P(t):t\in B_r\}\cup\{\sigma^r(i,i+2),\ \sigma^r(i+1,i+2)\}.$$
--
--   Thus $q_P(t)$ is the edge at $t$ whose dual edge avoids the corner $c^t_{\rho(t)}$, and the root contributes the two edges $\varepsilon^r_{i+2}$ and $\varepsilon^r_{i+1}$.
--
--   **Theorem.** For every black vertex $v$, the number of edges at $v$ that are not removed is
--
--   $$\bigl|\{e\in\operatorname{star}(v): e\notin R_i(P)\}\bigr|=\begin{cases}1,&\text{if } v=r,\\ 2,&\text{if } v\neq r.\end{cases}$$
--
--   These are exactly the degree conditions under which a forest with as many black as white vertices contains a perfect matching; combined with the fact that $E\setminus R_i(P)$ is a spanning tree when the opposite graph of $\rho$ is acyclic, they yield the perfect matching from which a Hamiltonian cycle is recovered. In the intended planar picture $N$ is a cubic bipartite plane graph, $D$ is its dual, and $c^v_0,c^v_1,c^v_2$ are the three faces around $v$.
--
--   **Formalization Note** The left-hand side is `((N.star v).filter fun e => e ∈ (M.removed P i)ᶜ).card`. In this statement the vertex type of $D$ need not be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Matching.lean#L443-L475

import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPolynomials
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Forest
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Contraction
import Definitions.Def_OAI_Combinatorics_Hamiltonian_MinorDuality
import Definitions.Def_OAI_Combinatorics_Hamiltonian_BMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Matching

open OAI OAI.Barnette OAI.Barnette.Network OAI.Barnette.Network.ColoredDual
open scoped Classical
open Barnette.TriangleSystem
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

omit [Fintype F] in
theorem OAI.Barnette.Network.ColoredDual.remainder_black_degree (P : (M.system root).Pair (M.nonroots root)) (hr : M.black root)
    (i : Fin 3) (v : V) (hv : M.black v) :
    ((N.star v).filter fun e => e ∈ (M.removed P i)ᶜ).card = if v = root then 1 else 2 := by sorry
