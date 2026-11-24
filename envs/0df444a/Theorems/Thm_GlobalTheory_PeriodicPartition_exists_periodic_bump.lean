-- Prove2me | Theorems.Thm_GlobalTheory_PeriodicPartition_exists_periodic_bump
-- name    : GlobalTheory.PeriodicPartition.exists_periodic_bump
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:43:20.565909+00:00
-- url     : https://prove2.me/theorems/42dbc584-bb03-43b4-b855-3a17bd0221c6
-- title:
--   Periodic Partition: exists periodic bump
-- statement:
--   The Periodic Partition construction uses the exists periodic bump property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmoothPeriodicPartitionOfUnity.lean#L30-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmoothPeriodicPartitionOfUnity.lean#L30-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmoothPeriodicPartitionOfUnity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real Topology
open GlobalTheory GlobalTheory.PeriodicPartition
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem GlobalTheory.PeriodicPartition.exists_periodic_bump (Λ : Submodule ℤ E) [DiscreteTopology Λ] {U : Set E}
    (hU : IsOpen U) (hper : ∀ (l : Λ) z, z ∈ U → z + l ∈ U) {x : E} (hx : x ∈ U) :
    ∃ ψ : E → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ (l : Λ) z, ψ (z + l) = ψ z) ∧ tsupport ψ ⊆ U ∧
      (∀ z, 0 ≤ ψ z) ∧ 0 < ψ x := by sorry
