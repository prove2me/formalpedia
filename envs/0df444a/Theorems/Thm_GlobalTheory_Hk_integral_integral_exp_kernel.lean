-- Prove2me | Theorems.Thm_GlobalTheory_Hk_integral_integral_exp_kernel
-- name    : GlobalTheory.Hk.integral_integral_exp_kernel
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:36:02.632621+00:00
-- url     : https://prove2.me/theorems/42d17e7a-d2a6-4537-8d6d-91a28bc21ab0
-- title:
--   Hk: integral integral exp kernel
-- statement:
--   The Hk construction uses the integral integral exp kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExpSumBounds.lean#L88-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExpSumBounds.lean#L88-L127

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

theorem GlobalTheory.Hk.integral_integral_exp_kernel (A : ℝ → ℂ) (hA : Measurable A) (K : ℝ)
    (hK : ∀ x : ℝ, 1 < x → ‖A x‖ ≤ K * Real.sqrt x) :
    ∫ t in Set.Ioi (0 : ℝ), ∫ x in Set.Ioi (1 : ℝ), A x * ((t * Real.exp (-(t * x)) : ℝ) : ℂ) =
      ∫ x in Set.Ioi (1 : ℝ), A x * (x : ℂ) ^ (-(1 : ℂ) - 1) := by sorry
