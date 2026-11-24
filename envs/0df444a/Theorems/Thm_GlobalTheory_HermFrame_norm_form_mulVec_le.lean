-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_norm_form_mulVec_le
-- name    : GlobalTheory.HermFrame.norm_form_mulVec_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:19:14.903819+00:00
-- url     : https://prove2.me/theorems/655a2737-9f79-4d34-9304-1956aca0dcea
-- title:
--   Herm Frame: norm form mul Vec le
-- statement:
--   The Herm Frame construction uses the norm form mul Vec le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L255-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L255-L259

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder MatrixOrder
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
variable {H : Matrix m m ℂ} {K : Matrix n n ℂ} {L : Matrix l l ℂ}

theorem GlobalTheory.HermFrame.norm_form_mulVec_le (hH : H.PosDef) (T : Matrix m m ℂ) (v : m → ℂ) :
    ‖form H (T *ᵥ v) v‖ ≤ opNorm H H T * gnorm H v ^ 2 := by sorry
