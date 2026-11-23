-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_form_sub_right
-- name    : GlobalTheory.HermFrame.form_sub_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:31.185788+00:00
-- url     : https://prove2.me/theorems/3f4a4b34-a84e-4742-bf16-7006bc98eec1
-- title:
--   Herm Frame: form sub right
-- statement:
--   The Herm Frame construction uses the form sub right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L45-L46

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

theorem GlobalTheory.HermFrame.form_sub_right (H : Matrix n n ℂ) (v w w' : n → ℂ) :
    form H v (w - w') = form H v w - form H v w' := by sorry
