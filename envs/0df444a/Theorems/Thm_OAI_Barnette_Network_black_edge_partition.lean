-- Prove2me | Theorems.Thm_OAI_Barnette_Network_black_edge_partition
-- name    : OAI.Barnette.Network.black_edge_partition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:40:52.509206+00:00
-- url     : https://prove2.me/theorems/b3f3ce7f-da0e-4cd3-813a-047560f3728d
-- title:
--   The stars of the black vertices partition the edges of a properly two-colored network
-- statement:
--   Let $N$ be an oriented network with finite vertex set $V$, finite edge set $E$, and tail and head maps $t,h:E\to V$. The star of $v\in V$ is $\operatorname{st}(v)=\{e\in E: t(e)=v\text{ or }h(e)=v\}$. Let $B\subseteq V$ be a set of black vertices such that every edge has exactly one black endpoint: $t(e)\in B$ if and only if $h(e)\notin B$.
--
--   **Theorem.** For every set of edges $K\subseteq E$
--
--   $$\sum_{v\in B}\big|\operatorname{st}(v)\cap K\big|=|K| .$$
--
--   Equivalently, the stars of the black vertices partition $E$, since every edge lies in the star of exactly one black vertex. With $K=E$ in a cubic graph this gives $|E|=3|B|$, and for smaller $K$ it counts the edges of $K$ by their black endpoints. This counting is used for minors of dual networks and for the face count of cubic bipartite plane graphs.
--
--   **Formalization Note** The black set is a predicate `black : V → Prop` and the sum runs over `Finset.univ.filter black`; $\operatorname{st}(v)\cap K$ is written `(N.star v).filter fun e => e ∈ K`. No simplicity or regularity is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/MinorDuality.lean#L158-L177

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

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype F] in
theorem OAI.Barnette.Network.black_edge_partition (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (K : Finset E) :
    ∑ v ∈ Finset.univ.filter black, ((N.star v).filter fun e => e ∈ K).card = K.card := by sorry
