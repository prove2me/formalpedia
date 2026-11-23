-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_conj_form
-- name    : GlobalTheory.HermFrame.conj_form
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:01:32.979693+00:00
-- url     : https://prove2.me/theorems/23dac5ee-5ef8-4a7e-96e6-6763cb48d0d5
-- title:
--   Herm Frame: conj form
-- statement:
--   The Herm Frame construction uses the conj form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L54-L59

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

theorem GlobalTheory.HermFrame.conj_form {H : Matrix n n ℂ} (hH : H.IsHermitian) (v w : n → ℂ) :
    conj (form H v w) = form H w v := by sorry
