-- Prove2me | Theorems.Thm_GlobalTheory_FoldIntegral_clm_integral_integral
-- name    : GlobalTheory.FoldIntegral.clm_integral_integral
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:33:55.847662+00:00
-- url     : https://prove2.me/theorems/9293b32f-543c-4d4d-8afb-4aed30b2e02b
-- title:
--   Fold Integral: clm integral integral
-- statement:
--   The Fold Integral construction uses the clm integral integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IntegralFoldViaLintegralFormula.lean#L31-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IntegralFoldViaLintegralFormula.lean#L31-L43

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

theorem GlobalTheory.FoldIntegral.clm_integral_integral {Y Z : Type} [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) (m : Measure Z) [SFinite m] (H : Y × Z → ℂ) (hH : Measurable H)
    (hfin : ∫⁻ y, ∫⁻ s, ‖H (y, s)‖ₑ ∂m ∂ν < ⊤) (L : ℂ →L[ℝ] ℝ) :
    L (∫ y, ∫ s, H (y, s) ∂m ∂ν) = ∫ y, ∫ s, L (H (y, s)) ∂m ∂ν := by sorry
