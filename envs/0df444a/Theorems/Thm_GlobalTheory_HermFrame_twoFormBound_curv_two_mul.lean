-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_twoFormBound_curv_two_mul
-- name    : GlobalTheory.HermFrame.twoFormBound_curv_two_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:39:27.134259+00:00
-- url     : https://prove2.me/theorems/dd5ac82b-8cf2-47b6-bc37-11e90d3e3ff0
-- title:
--   Herm Frame: two Form Bound curv two mul
-- statement:
--   The Herm Frame construction uses the two Form Bound curv two mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L660-L668
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L660-L668

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}
variable {ι : Type*} [Fintype ι]
variable [Fintype n]
variable {U : Set (ι → ℂ)} {H : (ι → ℂ) → Matrix n n ℂ} {G : (ι → ℂ) → Matrix ι ι ℂ} {C C' : ℝ}

theorem GlobalTheory.HermFrame.twoFormBound_curv_two_mul [DecidableEq n] (hH : IsPosFrame U H)
    (hG : ∀ z ∈ U, (G z).PosSemidef) (hC : 0 ≤ C)
    (h : ∀ z ∈ U, ∀ ξ v, ‖form (H z) (curv H z ξ ξ *ᵥ v) v‖ ≤
      C * gnorm (G z) ξ ^ 2 * gnorm (H z) v ^ 2) : TwoFormBound U H G (curv H) (2 * C) := by sorry
