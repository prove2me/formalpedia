-- Prove2me | Theorems.Thm_OAI_Barnette_Network_ColoredDual_pair_nonempty
-- name    : OAI.Barnette.Network.ColoredDual.pair_nonempty
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:46:52.121764+00:00
-- url     : https://prove2.me/theorems/362bad47-5864-4cc4-aadd-1d9c3e4bbbca
-- title:
--   Existence of a pair of partner corner states in a colored dual
-- statement:
--   Let $N$ and $D$ be oriented networks on a common finite edge set $E$, with finite vertex sets $V$ (for $N$) and $F$ (for $D$): every $e\in E$ has a tail $\operatorname{tail}(e)$ and a head $\operatorname{head}(e)$ in $V$, and a tail $\operatorname{tail}_D(e)$ and a head $\operatorname{head}_D(e)$ in $F$. The underlying simple graph of a network joins two distinct vertices when some edge has exactly these two endpoints. For $v\in V$ let $\operatorname{star}(v)\subseteq E$ be the set of edges with tail or head $v$ in $N$. Let $\nabla_N:\mathbb{R}^V\to\mathbb{R}^E$, $(\nabla_N f)(e)=f(\operatorname{head}(e))-f(\operatorname{tail}(e))$, be the gradient and $\partial_N:\mathbb{R}^E\to\mathbb{R}^V$, $(\partial_N x)(v)=\sum_{\operatorname{head}(e)=v}x_e-\sum_{\operatorname{tail}(e)=v}x_e$, the boundary map; $\nabla_D$ and $\partial_D$ are defined in the same way.
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
--   For $A\subseteq V$ let $\delta(A)\subseteq E$ be the set of edges with exactly one endpoint in $A$. Assume that $N$ is three-edge-connected and that all its three-edge cuts are trivial:
--
--   $$|\delta(A)|\ge 3\ \text{ whenever } \emptyset\neq A\subsetneq V,\qquad |\delta(A)|=3\implies |A|=1\ \text{or}\ |V\setminus A|=1.$$
--
--   Then for every black root $r$ there exists a pair of partner states:
--
--   $$\exists\ \text{states } \ell,\rho:B_r\to\mathbb{Z}/3\quad\text{with}\quad c^t_{\ell(t)}\neq c^t_{\rho(t)}\ \text{ for all } t\in B_r.$$
--
--   In the intended planar picture $N$ is a cubic bipartite plane graph, $D$ is its dual, and $c^v_0,c^v_1,c^v_2$ are the three faces around $v$. A state is then a system of distinct representatives assigning to each black vertex other than $r$ one of its faces, using every face that does not touch $r$ exactly once. Pairs of partner states are the configurations from which, under a further acyclicity condition, a Hamiltonian cycle of $N$ is later recovered; this theorem guarantees that the set of pairs is nonempty.
--
--   **Formalization Note** The conclusion is `Nonempty ((M.system root).Pair (M.nonroots root))`. States are index functions into `Fin 3` on the subtype `M.Black root`, the set $X_r$ is `M.nonroots root`, and the two connectivity hypotheses are `N.ThreeEdgeConnected` and `N.TrivialThreeCuts` (both phrased with finite sets of vertices and their complements).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/BMatching.lean#L403-L427

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

open OAI OAI.Barnette OAI.Barnette.Network OAI.Barnette.Network.ColoredDual
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D)

theorem OAI.Barnette.Network.ColoredDual.pair_nonempty (hcut : N.ThreeEdgeConnected) (htr : N.TrivialThreeCuts)
    (root : V) (hr : M.black root) : Nonempty ((M.system root).Pair (M.nonroots root)) := by sorry
