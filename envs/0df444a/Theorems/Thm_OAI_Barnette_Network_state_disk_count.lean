-- Prove2me | Theorems.Thm_OAI_Barnette_Network_state_disk_count
-- name    : OAI.Barnette.Network.state_disk_count
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:19:05.598982+00:00
-- url     : https://prove2.me/theorems/0197159c-d91a-4e56-854a-04d3455fdb7c
-- title:
--   Counting the dual vertices of a disk bounded by a state cycle
-- statement:
--   **Setting.** Let $N$ and $D$ be networks on a common finite edge set $E$ with finite vertex sets $V$ and $F$; every edge $e$ has a tail and a head, $t_N(e),h_N(e)\in V$ in $N$ and $t_D(e),h_D(e)\in F$ in $D$, and $e$ is *incident* to its tail and its head. Write $\nabla_N f(e)=f(h_N(e))-f(t_N(e))$ and $\partial_N x(v)=\sum_{e:\,h_N(e)=v}x(e)-\sum_{e:\,t_N(e)=v}x(e)$, and similarly for $D$; let $G(N)$, $G(D)$ be the underlying simple graphs (distinct vertices adjacent when some edge joins them). Assume $N$ and $D$ are *dual*: $G(N)$ and $G(D)$ are connected, $\ker\partial_N=\operatorname{im}\nabla_D$ and $\ker\partial_D=\operatorname{im}\nabla_N$. Assume $D$ is *simple* (no loops, no two edges with the same endpoint pair), and that for every $v\in V$ a triangle $T_v$ of $D$ is given whose edge set is the star $\operatorname{st}_N(v)$ of edges incident to $v$ in $N$; a triangle consists of distinct corners $u_0,u_1,u_2\in F$ and distinct edges $f_0,f_1,f_2$ such that $f_j$ joins $u_j$ and $u_{j+1}$ (indices mod $3$).
--
--   Let $B\subseteq V$ be a set of black vertices such that every edge has exactly one black endpoint, denoted $b(e)$. Fix a root $\rho\in V$ and a map $m:V\to F$ such that
--
--   1. $m$ is injective on $B\setminus\{\rho\}$;
--   2. $m(v)$ is a corner of $T_v$ for every $v\in B\setminus\{\rho\}$;
--   3. a vertex $z\in F$ is not a corner of $T_\rho$ if and only if $z=m(v)$ for some $v\in B\setminus\{\rho\}$.
--
--   Let $c_0,\dots,c_{k-1}$ ($k\ge3$) be distinct vertices of $F$ forming a cycle of $G(D)$ ($c_i$ adjacent to $c_{i+1}$, indices mod $k$), and let $e_i$ be the edge of $D$ joining $c_i$ and $c_{i+1}$ (unique since $D$ is simple). Assume that $b(e_i)\neq\rho$ and $m(b(e_i))=c_i$ for every $i$.
--
--   **Statement.** For $A\subseteq V$ let $\delta(A)$ be the set of edges with exactly one $N$-endpoint in $A$, $\delta_B(A)=\{e\in\delta(A): b(e)\in A\}$, $E_A$ the set of edges with at least one $N$-endpoint in $A$, and $F_A$ the set of vertices of $D$ incident in $D$ to an edge of $E_A$. If $\rho\notin A$ and $\delta(A)=\{e_0,\dots,e_{k-1}\}$, then
--
--   $$
--   |A\cap B|+|\delta(A)|=|F_A|+|\delta_B(A)|.
--   $$
--
--   The map $m$ is an incidence state: it selects one corner in the triangle of each black non-root vertex so that every dual vertex off the root triangle is selected exactly once. A cycle of $D$ whose $i$-th edge belongs to the triangle of $b(e_i)$ and starts at the selected corner $c_i=m(b(e_i))$ is a state cycle. The identity counts the dual vertices of the disk cut out by such a cycle. When in addition $N$ is simple and cubic and both $A$ and $V\setminus A$ induce connected subgraphs, combining it with the disk Euler formula and the two cubic edge counts forces $|\delta(A)|=2|\delta_B(A)|+3$.
--
--   **Formalization Note** The cycle is a term `C : CycleCoordinates D.graph`, i.e. an injective map from $\mathbb{Z}/(n+3)$ to $F$ with consecutive vertices adjacent, so $k=n+3$; $e_i$ is `D.cycleEdge C i`, an edge chosen among those joining $c_i$ and $c_{i+1}$. The black endpoint is `N.blackEndpoint black e`, $\delta_B(A)$ is `N.blackCut black A`, and $F_A$ is `N.regionVertices D A`. The map $m$ is a total function, but only its values on black non-root vertices matter. Neither $N$ being simple nor cubic is assumed here.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/StateDisk.lean#L260-L373

import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

theorem OAI.Barnette.Network.state_disk_count (h : N.Duality D) (sD : D.Simple)
    (face : ∀ v, D.Triangle (N.star v)) (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (root : V)
    (m : V → F)
    (hm_inj : Set.InjOn m {v | black v ∧ v ≠ root})
    (hm_face : ∀ v, black v → v ≠ root → m v ∈ Set.range (face v).corner)
    (hm_range : ∀ z, z ∉ Set.range (face root).corner ↔
      ∃ v, black v ∧ v ≠ root ∧ m v = z)
    (C : Barnette.CycleCoordinates D.graph)
    (hchoice : ∀ i, N.blackEndpoint black (D.cycleEdge C i) ≠ root ∧
      m (N.blackEndpoint black (D.cycleEdge C i)) = C.vertex i)
    (A : Finset V) (hroot : root ∉ A) (hcut : N.cut A = D.cycleEdges C) :
    (A.filter black).card + (N.cut A).card =
      (N.regionVertices D A).card + (N.blackCut black A).card := by sorry
