-- Prove2me | Theorems.Thm_OAI_Barnette_Network_Duality_minor
-- name    : OAI.Barnette.Network.Duality.minor
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T03:04:27.98296+00:00
-- url     : https://prove2.me/theorems/db9e54f6-4606-49ff-a15f-560a843c0adb
-- title:
--   Algebraic planar duality passes to minors obtained by contracting connected fibers and deleting edges
-- statement:
--   A *network* $N$ consists of finite sets $V$ (vertices) and $E$ (edges) together with maps $t,h:E\to V$ giving the tail and the head of each edge; parallel edges and loops are allowed a priori. Its underlying simple graph $G(N)$ joins $v\neq w$ whenever some edge has endpoints $v$ and $w$. The *gradient* $\nabla_N:\mathbb{R}^V\to\mathbb{R}^E$ and the *boundary* $\partial_N:\mathbb{R}^E\to\mathbb{R}^V$ are
--   $$(\nabla_N f)(e)=f(h(e))-f(t(e)),\qquad(\partial_N x)(v)=\sum_{e:\,h(e)=v}x_e-\sum_{e:\,t(e)=v}x_e .$$
--   Two networks $N$ on $V$ and $D$ on a finite set $F$ with the **same** edge set $E$ are called *dual* if $G(N)$ and $G(D)$ are connected and
--   $$\ker\partial_N=\operatorname{im}\nabla_D,\qquad\ker\partial_D=\operatorname{im}\nabla_N,$$
--   i.e. the cycle space of each network is the cut space of the other.
--
--   Let $q:V\to W$ be a map to a finite set. An edge $e$ is *$q$-internal* if $q(t(e))=q(h(e))$, and $q$ has *connected fibers* if any two vertices $v,w$ with $q(v)=q(w)$ are joined by a path in the underlying graph of the subnetwork of $q$-internal edges. Let $j:K\to E$ be a map from a finite set $K$. The network $M$ has vertex set $W$, edge set $K$, and
--   $$t_M(k)=q\bigl(t(j(k))\bigr),\qquad h_M(k)=q\bigl(h(j(k))\bigr).$$
--
--   **Theorem.** Let $N$ (on $V$) and $D$ (on $F$) be dual networks with edge set $E$. Assume that $q:V\to W$ is surjective with connected fibers, that $j:K\to E$ is injective, that every selected edge is external, $q(t(j(k)))\neq q(h(j(k)))$ for all $k\in K$, and that $G(M)$ is connected. Then there exist a finite set $L$ and a network $D'$ with vertex set $L$ and edge set $K$ such that
--
--   $$
--   M\ \text{and}\ D'\ \text{are dual}:\qquad \ker\partial_M=\operatorname{im}\nabla_{D'},\quad \ker\partial_{D'}=\operatorname{im}\nabla_M,\quad G(M),\,G(D')\ \text{connected}.
--   $$
--
--   The network $M$ is the minor of $N$ obtained by contracting the $q$-internal edges (which collapses each fiber of $q$ to one vertex) and deleting all edges outside $j(K)$. The theorem says that this algebraic form of planar duality is inherited by such minors. It is used to give a dual network to the graph obtained by capping one side of a 3-edge cut, and to graphs realized as minors of a network that already has a dual.
--
--   **Formalization Note** The duality relation is the structure `N.Duality D`; the minor is `(N.mapVertices q).restrict j`, and connected fibers is `N.ConnectedFibers q`. The new vertex type `L` is produced in the same universe as `F`, with a `Fintype` instance.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/CappedDuality.lean#L62-L137

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
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ForestMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ThreeCuts

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
universe uF
variable {V E W K : Type*} {F : Type uF} [Fintype V] [Fintype E] [Fintype F]
  [Fintype W] [Fintype K]

theorem OAI.Barnette.Network.Duality.minor (N : Network V E) (D : Network F E) (h : N.Duality D)
    (q : V → W) (hq : Function.Surjective q) (hc : N.ConnectedFibers q)
    (j : K → E) (hj : Function.Injective j)
    (hjext : ∀ k, q (N.tail (j k)) ≠ q (N.head (j k)))
    (hM : ((N.mapVertices q).restrict j).graph.Connected) :
    ∃ (L : Type uF) (_ : Fintype L) (dual : Network L K),
      ((N.mapVertices q).restrict j).Duality dual := by sorry
