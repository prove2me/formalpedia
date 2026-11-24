-- Prove2me | Theorems.Thm_GlobalTheory_JR_integral_eq_zero_of_shift_mul
-- name    : GlobalTheory.JR.integral_eq_zero_of_shift_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:38:22.009728+00:00
-- url     : https://prove2.me/theorems/e506cdba-874f-4f38-b87d-0ad0cedec7c2
-- title:
--   JR: integral eq zero of shift mul
-- statement:
--   The JR construction uses the integral eq zero of shift mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HasCompactSupportPartialFourierGLBlock.lean#L8-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HasCompactSupportPartialFourierGLBlock.lean#L8-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HasCompactSupportPartialFourierGLBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR

theorem GlobalTheory.JR.integral_eq_zero_of_shift_mul {V : Type} [AddGroup V] [MeasurableSpace V] [MeasurableAdd V]
    (μ : Measure V) [μ.IsAddRightInvariant] (g : V → ℂ) (t : V) (z : ℂ) (hz : z ≠ 1)
    (h : ∀ x, g (x + t) = g x * z) : ∫ x, g x ∂μ = 0 := by sorry
