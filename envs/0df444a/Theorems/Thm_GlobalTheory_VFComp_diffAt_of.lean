-- Prove2me | Theorems.Thm_GlobalTheory_VFComp_diffAt_of
-- name    : GlobalTheory.VFComp.diffAt_of
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:50:24.006639+00:00
-- url     : https://prove2.me/theorems/1a51605d-d4da-499c-b1bd-8652a64f6f9a
-- title:
--   VFComp: diff At of
-- statement:
--   The VFComp construction uses the diff At of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoefVFContDiffOn.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoefVFContDiffOn.lean#L20-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoefVFContDiffOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
noncomputable section
open GlobalTheory GlobalTheory.VFComp
variable {d : ℕ}

theorem GlobalTheory.VFComp.diffAt_of {U : Set (E d)} (hU : IsOpen U) {f : E d → ℂ} (hf : ContDiffOn ℝ ∞ f U)
    {x : E d} (hx : x ∈ U) : DifferentiableAt ℝ f x := by sorry
