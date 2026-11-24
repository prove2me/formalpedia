-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_form_self
-- name    : GlobalTheory.HermFrame.form_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:29.721427+00:00
-- url     : https://prove2.me/theorems/e1c42924-f12d-47cd-9c15-74b1333da3b1
-- title:
--   Herm Frame: form self
-- statement:
--   The Herm Frame construction uses the form self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L92-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L92-L95

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

theorem GlobalTheory.HermFrame.form_self {H : Matrix n n ℂ} (hH : H.PosSemidef) (v : n → ℂ) :
    form H v v = ((gnorm H v ^ 2 : ℝ) : ℂ) := by sorry
