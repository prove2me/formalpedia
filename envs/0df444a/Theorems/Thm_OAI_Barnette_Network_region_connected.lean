-- Prove2me | Theorems.Thm_OAI_Barnette_Network_region_connected
-- name    : OAI.Barnette.Network.region_connected
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:11:56.730639+00:00
-- url     : https://prove2.me/theorems/07d8c08d-84d0-4eeb-8ffb-9b3bb37bfd27
-- title:
--   The dual region around a connected vertex set is connected
-- statement:
--   Let $N$ and $D$ be networks on a common finite edge set $E$, where $N$ has vertex set $V$ and $D$ has a finite vertex set $F$. Every edge $e$ has a tail and a head in each network, written $t_N(e),h_N(e)\in V$ and $t_D(e),h_D(e)\in F$; the edge $e$ is *incident* to a vertex if that vertex is its tail or its head. The underlying graph $G(N)$ is the simple graph on $V$ in which two distinct vertices are adjacent when some edge has exactly these two endpoints (in either order); $G(D)$ is defined in the same way. The network $D$ is *simple* if it has no loops and no two of its edges have the same unordered pair of endpoints. For $v\in V$ let $\operatorname{st}_N(v)\subseteq E$ be the set of edges incident to $v$ in $N$. A *triangle* of $D$ with edge set $s\subseteq E$ consists of three distinct vertices $c_0,c_1,c_2\in F$ (its corners) and three distinct edges $e_0,e_1,e_2$ with $\{e_0,e_1,e_2\}=s$ such that $e_i$ has the endpoints $\{c_i,c_{i+1}\}$ in $D$, indices taken modulo $3$.
--
--   For a finite set $A\subseteq V$ let $E_A\subseteq E$ be the set of edges having at least one $N$-endpoint in $A$, and let $F_A\subseteq F$ be the set of vertices of $D$ that are incident in $D$ to some edge of $E_A$. The *region* of $A$ is the network $R_A$ with vertex set $F_A$ and edge set $E_A$, in which every edge keeps its $D$-tail and its $D$-head.
--
--   Suppose that the subgraph of $G(N)$ induced on $A$ is connected, that $D$ is simple, and that for every $v\in V$ a triangle $T_v$ of $D$ with edge set $\operatorname{st}_N(v)$ is given. Then
--
--   $$
--   G(R_A)\ \text{is a connected graph.}
--   $$
--
--   In the intended application $N$ is a cubic plane graph and $D$ is its dual triangulation, so $T_v$ is the dual triangle around the vertex $v$ and $R_A$ is the patch of the dual made of the triangles $T_v$, $v\in A$. Connectedness of this patch is what allows the rank formula for cycle spaces of connected networks to be applied to $R_A$; it is one ingredient of the Euler-type count $|A|+|F_A|=|E_A|+1$ for regions whose complement is also connected.
--
--   **Formalization Note** Mathlib's notion of a connected graph includes nonemptiness, so the hypothesis forces $A\neq\emptyset$. The triangles are supplied as data, `face : ∀ v, D.Triangle (N.star v)`, and the vertex type $V$ is not required to be finite. The region network is `N.region D A`, with vertex set `N.regionVertices D A` and edge set `N.regionEdges A`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/DiskRegions.lean#L72-L151

import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] in
theorem OAI.Barnette.Network.region_connected (A : Finset V) (hA : (N.graph.induce {v | v ∈ A}).Connected)
    (sD : D.Simple) (face : ∀ v, D.Triangle (N.star v)) :
    (N.region D A).graph.Connected := by sorry
