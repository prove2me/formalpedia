-- Prove2me | Theorems.Thm_GlobalTheory_PeriodicPartition_exists_partition
-- name    : GlobalTheory.PeriodicPartition.exists_partition
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:15:21.494099+00:00
-- url     : https://prove2.me/theorems/23150320-ae07-48e8-938a-e56a5af76d78
-- title:
--   Periodic Partition: exists partition
-- statement:
--   The Periodic Partition construction uses the exists partition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmoothPeriodicPartitionOfUnity.lean#L91-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmoothPeriodicPartitionOfUnity.lean#L91-L125

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

theorem GlobalTheory.PeriodicPartition.exists_partition (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {ι : Type} (U : ι → Set E) (hU : ∀ i, IsOpen (U i))
    (hper : ∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i) (hcov : ∀ z, ∃ i, z ∈ U i) :
    ∃ (s : Finset ι) (ρ : ι → E → ℝ), (∀ i, ContDiff ℝ ∞ (ρ i) ∧
      (∀ (l : Λ) z, ρ i (z + l) = ρ i z) ∧ tsupport (ρ i) ⊆ U i) ∧
      ∀ z, ∑ i ∈ s, ρ i z = 1 := by sorry
