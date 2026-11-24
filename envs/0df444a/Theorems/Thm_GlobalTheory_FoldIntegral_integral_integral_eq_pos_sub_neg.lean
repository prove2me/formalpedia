-- Prove2me | Theorems.Thm_GlobalTheory_FoldIntegral_integral_integral_eq_pos_sub_neg
-- name    : GlobalTheory.FoldIntegral.integral_integral_eq_pos_sub_neg
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:33:45.424248+00:00
-- url     : https://prove2.me/theorems/f6dffe60-4585-4d12-bc48-cb9feb4eb668
-- title:
--   Fold Integral: integral integral eq pos sub neg
-- statement:
--   The Fold Integral construction uses the integral integral eq pos sub neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IntegralFoldViaLintegralFormula.lean#L6-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IntegralFoldViaLintegralFormula.lean#L6-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralFoldViaLintegralFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.FoldIntegral

theorem GlobalTheory.FoldIntegral.integral_integral_eq_pos_sub_neg {Y Z : Type} [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) (m : Measure Z) [SFinite m] (h : Y × Z → ℝ) (hh : Measurable h)
    (hfin : ∫⁻ y, ∫⁻ s, ‖h (y, s)‖ₑ ∂m ∂ν < ⊤) :
    ∫ y, ∫ s, h (y, s) ∂m ∂ν =
      (∫⁻ y, ∫⁻ s, ENNReal.ofReal (h (y, s)) ∂m ∂ν).toReal -
        (∫⁻ y, ∫⁻ s, ENNReal.ofReal (-h (y, s)) ∂m ∂ν).toReal := by sorry
