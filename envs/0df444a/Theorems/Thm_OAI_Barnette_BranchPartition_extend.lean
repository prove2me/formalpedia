-- Prove2me | Theorems.Thm_OAI_Barnette_BranchPartition_extend
-- name    : OAI.Barnette.BranchPartition.extend
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T03:16:52.045359+00:00
-- url     : https://prove2.me/theorems/e2127717-5269-4770-8b1c-a11dcaa7edd1
-- title:
--   Disjoint connected branch sets in a connected finite graph extend to a partition into connected parts
-- statement:
--   Let $H$ be a simple graph on a finite vertex set $W$, and for $S\subseteq W$ let $H[S]$ be the subgraph induced on $S$. Let $V$ be a finite nonempty index set.
--
--   **Theorem.** Assume $H$ is connected, and let $(B^0_v)_{v\in V}$ be subsets of $W$ such that each $H[B^0_v]$ is connected (in particular $B^0_v\neq\varnothing$) and $B^0_v\cap B^0_w=\varnothing$ for $v\neq w$. Then there are subsets $(B_v)_{v\in V}$ of $W$ such that
--
--   $$
--   B^0_v\subseteq B_v,\qquad H[B_v]\ \text{connected},\qquad B_v\cap B_w=\varnothing\ \ (v\neq w),\qquad \bigcup_{v\in V}B_v=W .
--   $$
--
--   In words, any family of pairwise disjoint connected vertex sets in a connected finite graph can be enlarged to a partition of all vertices into connected parts, each containing the original set. It is the first step in turning a minor model (disjoint connected branch sets) into a surjective quotient map $W\to V$ with connected fibers, the form in which minors are handled by contraction and deletion.
--
--   **Formalization Note** Connectedness of $H[S]$ is Mathlib's `(H.induce S).Connected`, which includes nonemptiness of $S$; the covering condition is stated as: for every $w\in W$ there is $v$ with $w\in B_v$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/BranchPartition.lean#L26-L98

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

theorem OAI.Barnette.BranchPartition.extend (hH : H.Connected) (B₀ : V → Set W)
    (hB₀ : ∀ v, (H.induce (B₀ v)).Connected)
    (hd₀ : ∀ v w, v ≠ w → Disjoint (B₀ v) (B₀ w)) :
    ∃ B : V → Set W,
      (∀ v, B₀ v ⊆ B v) ∧
      (∀ v, (H.induce (B v)).Connected) ∧
      (∀ v w, v ≠ w → Disjoint (B v) (B w)) ∧
      (∀ w, ∃ v, w ∈ B v) := by sorry
