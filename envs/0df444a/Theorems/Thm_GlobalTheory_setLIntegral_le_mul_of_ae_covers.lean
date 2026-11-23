-- Prove2me | Theorems.Thm_GlobalTheory_setLIntegral_le_mul_of_ae_covers
-- name    : GlobalTheory.setLIntegral_le_mul_of_ae_covers
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:06.434357+00:00
-- url     : https://prove2.me/theorems/b50052c0-e4d6-41d4-a82c-c67d030330a7
-- title:
--   Global Theory: set LIntegral le mul of ae covers
-- statement:
--   The Global Theory construction uses the set LIntegral le mul of ae covers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L68-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L68-L94

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

theorem GlobalTheory.setLIntegral_le_mul_of_ae_covers (hD : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D)
    (hB : NullMeasurableSet B μ) {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x)
    {m : ℝ≥0∞} (hm : ∀ᵐ x ∂μ.restrict D, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ≤ m) :
    ∫⁻ x in B, u x ∂μ ≤ m * ∫⁻ x in D, u x ∂μ := by sorry
