-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_form_adj
-- name    : GlobalTheory.HermFrame.form_adj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:09:31.574998+00:00
-- url     : https://prove2.me/theorems/eee7f897-17c7-43bf-84eb-dceb7e764073
-- title:
--   Herm Frame: form adj
-- statement:
--   The Herm Frame construction uses the form adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L129-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L129-L135

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

theorem GlobalTheory.HermFrame.form_adj [DecidableEq m] {H : Matrix m m ℂ} {K : Matrix n n ℂ} (hH : H.IsHermitian)
    (hu : IsUnit H.det) (hK : K.IsHermitian) (T : Matrix n m ℂ) (v : m → ℂ) (w : n → ℂ) :
    form K (T *ᵥ v) w = form H v (adj H K T *ᵥ w) := by sorry
