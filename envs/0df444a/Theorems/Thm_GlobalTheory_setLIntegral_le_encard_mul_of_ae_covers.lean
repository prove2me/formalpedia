-- Prove2me | Theorems.Thm_GlobalTheory_setLIntegral_le_encard_mul_of_ae_covers
-- name    : GlobalTheory.setLIntegral_le_encard_mul_of_ae_covers
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:08.36979+00:00
-- url     : https://prove2.me/theorems/5b3853df-1a9b-450d-8078-1daa06c05434
-- title:
--   Global Theory: set LIntegral le encard mul of ae covers
-- statement:
--   The Global Theory construction uses the set LIntegral le encard mul of ae covers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L127-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L127-L132

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Pointwise
open GlobalTheory
variable {G X : Type*} [Group G] [MulAction G X]
variable [MeasurableSpace X] {μ : Measure X} [MeasurableConstSMul G X]
  [SMulInvariantMeasure G X μ] [Countable G] {B D : Set X}

theorem GlobalTheory.setLIntegral_le_encard_mul_of_ae_covers (hD : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D)
    (hB : NullMeasurableSet B μ) {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ∫⁻ x in B, u x ∂μ
      ≤ ({g : G | (g • B ∩ B).Nonempty}.encard : ℝ≥0∞) * ∫⁻ x in D, u x ∂μ := by sorry
