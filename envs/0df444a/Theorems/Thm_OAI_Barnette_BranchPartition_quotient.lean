-- Prove2me | Theorems.Thm_OAI_Barnette_BranchPartition_quotient
-- name    : OAI.Barnette.BranchPartition.quotient
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T03:19:03.509462+00:00
-- url     : https://prove2.me/theorems/de078e2b-65cc-46e5-95b4-8fe2a0a1c1d1
-- title:
--   A partition into connected vertex sets is the fibre partition of a surjection
-- statement:
--   Let $H$ be a simple graph on a vertex set $W$, and let $V$ be an index set. For a subset $B \subseteq W$ write $H[B]$ for the subgraph of $H$ induced on $B$. Suppose $(B_v)_{v \in V}$ is a family of subsets of $W$ such that
--
--   1. for every $v \in V$ the induced subgraph $H[B_v]$ is connected (in particular $B_v \neq \emptyset$);
--   2. the sets are pairwise disjoint: $B_v \cap B_w = \emptyset$ whenever $v \neq w$;
--   3. the sets cover $W$: every $w \in W$ lies in some $B_v$.
--
--   Then there is a surjective map $q : W \to V$ whose fibres are exactly the given sets:
--
--   $$
--   q(w) = v \iff w \in B_v \qquad \text{for all } w \in W,\ v \in V .
--   $$
--
--   Thus a partition of the vertices of $H$ into connected pieces indexed by $V$ is encoded by a surjection onto $V$ whose fibres are exactly these pieces; $q$ sends each vertex to the index of the piece containing it. In minor constructions this is the contraction map that collapses each branch set of a minor model, once the branch sets have been enlarged to a partition of the host graph, to a single vertex.
--
--   **Formalization Note** The induced subgraph is `H.induce (B v)` and connectivity is Mathlib's `SimpleGraph.Connected`, which includes nonemptiness of the vertex set; this is why hypothesis 1 forces every $B_v$ to be nonempty. No finiteness of $V$ or $W$ is assumed (the section's `Fintype` and `Nonempty` assumptions are omitted for this theorem).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/BranchPartition.lean#L100-L117

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
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Gluing
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Traces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_SquareGrid
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Corridors
import Definitions.Def_OAI_Combinatorics_Hamiltonian_MinorModel

open OAI OAI.Barnette
open scoped Classical
variable {V W : Type*} [Fintype V] [Fintype W] [Nonempty V]
  (H : SimpleGraph W)

omit [Fintype V] [Fintype W] [Nonempty V] in
theorem OAI.Barnette.BranchPartition.quotient (B : V → Set W)
    (hB : ∀ v, (H.induce (B v)).Connected)
    (hd : ∀ v w, v ≠ w → Disjoint (B v) (B w))
    (hcover : ∀ w, ∃ v, w ∈ B v) :
    ∃ q : W → V, Function.Surjective q ∧ (∀ w v, q w = v ↔ w ∈ B v) := by sorry
