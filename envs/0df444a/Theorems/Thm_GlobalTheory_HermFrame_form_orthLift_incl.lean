-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_form_orthLift_incl
-- name    : GlobalTheory.HermFrame.form_orthLift_incl
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:06:59.592637+00:00
-- url     : https://prove2.me/theorems/0d99734f-0439-5eb1-aec3-5a8d2d35e166
-- title:
--   Herm Frame: form orth Lift incl
-- statement:
--   The Herm Frame construction uses the form orth Lift incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L396-L400
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L396-L400

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
variable [DecidableEq m] [DecidableEq l]
variable {H : Matrix (m ⊕ l) (m ⊕ l) ℂ}

theorem GlobalTheory.HermFrame.form_orthLift_incl (hu : IsUnit (subGram H).det) (q : l → ℂ) (u : m → ℂ) :
    form H (orthLift H *ᵥ q) (incl m l *ᵥ u) = 0 := by sorry
