-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_form_smul_left
-- name    : GlobalTheory.HermFrame.form_smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:01:41.410709+00:00
-- url     : https://prove2.me/theorems/a3297d3b-e53c-4736-bfc9-4593af2d8dbb
-- title:
--   Herm Frame: form smul left
-- statement:
--   The Herm Frame construction uses the form smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L36-L37

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

theorem GlobalTheory.HermFrame.form_smul_left (H : Matrix n n ℂ) (c : ℂ) (v w : n → ℂ) :
    form H (c • v) w = c * form H v w := by sorry
