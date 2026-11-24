-- Prove2me | Theorems.Thm_GlobalTheory_exists_smooth_periodic_partition_of_unity
-- name    : GlobalTheory.exists_smooth_periodic_partition_of_unity
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:42:17.331991+00:00
-- url     : https://prove2.me/theorems/d75fb216-723c-4bde-8371-c2a8c70e6c39
-- title:
--   Global Theory: exists smooth periodic partition of unity
-- statement:
--   The Global Theory construction uses the exists smooth periodic partition of unity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmoothPeriodicPartitionOfUnity.lean#L196-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmoothPeriodicPartitionOfUnity.lean#L196-L277

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
open GlobalTheory
open Complex Matrix
open scoped ContDiff BigOperators Real Topology Manifold

theorem GlobalTheory.exists_smooth_periodic_partition_of_unity :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (ι : Type) (U : ι → Set (Fin g → ℂ)), (∀ i, IsOpen (U i)) → (∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i) → (∀ z, ∃ i, z ∈ U i) → ∃ (s : Finset ι) (ρ : ι → (Fin g → ℂ) → ℝ), (∀ i, ContDiff ℝ ∞ (ρ i) ∧ (∀ (l : Λ) z, ρ i (z + l) = ρ i z) ∧ tsupport (ρ i) ⊆ U i) ∧ ∀ z, ∑ i ∈ s, ρ i z = 1 := by sorry
