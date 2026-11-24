-- Prove2me | Theorems.Thm_GlobalTheory_Hk_integral_mul_exp_neg_sq
-- name    : GlobalTheory.Hk.integral_mul_exp_neg_sq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:35:58.849976+00:00
-- url     : https://prove2.me/theorems/024acad3-9348-490f-a02b-23914a3dd522
-- title:
--   Hk: integral mul exp neg sq
-- statement:
--   The Hk construction uses the integral mul exp neg sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExpSumBounds.lean#L75-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExpSumBounds.lean#L75-L86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk

theorem GlobalTheory.Hk.integral_mul_exp_neg_sq {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-(t * x))) (Set.Ioi 0) ∧
    ∫ t in Set.Ioi 0, t * Real.exp (-(t * x)) = x ^ (-2 : ℝ) := by sorry
