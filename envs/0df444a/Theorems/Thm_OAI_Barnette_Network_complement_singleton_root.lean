-- Prove2me | Theorems.Thm_OAI_Barnette_Network_complement_singleton_root
-- name    : OAI.Barnette.Network.complement_singleton_root
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:37:51.290836+00:00
-- url     : https://prove2.me/theorems/bdfa5e29-6b3c-42c5-839f-ba9936be8d15
-- title:
--   A rim-three region missing a single vertex misses the root
-- statement:
--   Let $N$ (vertex set $V$) and $D$ (vertex set $F$) be oriented networks on a common edge set $E$, with $V$ and $E$ finite, given by tail and head maps $t_N,h_N:E\to V$ and $t_D,h_D:E\to F$. For a finite set $U\subseteq F$ of dual vertices, the induced edges are $E_D[U]=\{e\in E: t_D(e)\in U\text{ and }h_D(e)\in U\}$. Deleting them from $N$ leaves the network on $V$ with edge set $E\setminus E_D[U]$. Its regions are the connected components of its underlying simple graph (distinct vertices adjacent when an edge joins them), and the shore $A_q\subseteq V$ of a region $q$ is the set of vertices of $q$. The rim of $q$ counts the ends of induced edges lying on the shore:
--   $$\operatorname{rim}(q)=\sum_{e\in E_D[U]}\big([t_N(e)\in A_q]+[h_N(e)\in A_q]\big),$$
--   where $[\cdot]$ is the Iverson bracket. Let $\operatorname{st}(v)=\{e: t_N(e)=v\text{ or }h_N(e)=v\}$ be the star of $v\in V$. The network $N$ is simple if it has no loops and distinct edges have distinct unordered endpoint pairs. It is three-edge-connected if every $A\subseteq V$ with $A\ne\varnothing\ne V\setminus A$ is crossed by at least three edges, i.e. at least three edges have exactly one endpoint in $A$.
--
--   **Theorem.** Suppose $N$ is simple, three-edge-connected, and its underlying graph is $3$-regular. Let $U\subseteq F$ be finite and let $\rho\in V$ be a vertex whose whole star is induced, $\operatorname{st}(\rho)\subseteq E_D[U]$. If $q$ is a region with $\operatorname{rim}(q)=3$ whose shore misses exactly one vertex $v$, then that vertex is $\rho$:
--
--   $$\operatorname{st}(\rho)\subseteq E_D[U],\quad \operatorname{rim}(q)=3,\quad V\setminus A_q=\{v\}\qquad\Longrightarrow\qquad v=\rho .$$
--
--   In other words, when all edges at the root are induced, any region of rim three whose complement is a single vertex consists of all vertices other than the root. This identifies the trivial three-edge cuts that arise when a dual network is contracted around the root.
--
--   **Formalization Note** The hypotheses are `hN : N.Simple`, `h3 : N.graph.IsRegularOfDegree 3`, `hcut : N.ThreeEdgeConnected`, `hr : N.star root ⊆ D.inducedEdges U`, `hq : N.rim D U q = 3` and `hv : (N.regionShore D U q)ᶜ = {v}`. The dual vertex type $F$ need not be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Contraction.lean#L406-L424

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

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype F] in
theorem OAI.Barnette.Network.complement_singleton_root (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (hcut : N.ThreeEdgeConnected) (U : Finset F) (root : V)
    (hr : N.star root ⊆ D.inducedEdges U) (q : N.Regions D U)
    (hq : N.rim D U q = 3) {v : V} (hv : (N.regionShore D U q)ᶜ = {v}) : v = root := by sorry
