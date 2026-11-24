-- Prove2me | Theorems.Thm_GlobalTheory_Hk_integral_mul_exp_neg_Ioi
-- name    : GlobalTheory.Hk.integral_mul_exp_neg_Ioi
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:36:19.686835+00:00
-- url     : https://prove2.me/theorems/41f8641e-ab94-4366-8b68-b0e885ebe259
-- title:
--   Hk: integral mul exp neg Ioi
-- statement:
--   The Hk construction uses the integral mul exp neg Ioi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExpSumBounds.lean#L8-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExpSumBounds.lean#L8-L16

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

theorem GlobalTheory.Hk.integral_mul_exp_neg_Ioi {t : ℝ} (ht : 0 < t) (y : ℝ) :
    IntegrableOn (fun x : ℝ => t * Real.exp (-(t * x))) (Set.Ioi y) ∧
    ∫ x in Set.Ioi y, t * Real.exp (-(t * x)) = Real.exp (-(t * y)) := by sorry
