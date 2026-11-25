-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_form_secondFormAdj_mul
-- name    : GlobalTheory.HermFrame.form_secondFormAdj_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:06:57.912265+00:00
-- url     : https://prove2.me/theorems/8d934591-3de4-5e0d-871f-ee6c678535bd
-- title:
--   Herm Frame: form second Form Adj mul
-- statement:
--   The Herm Frame construction uses the form second Form Adj mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L805-L809
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L805-L809

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}
variable [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
variable {U : Set E} {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E} {k : WithTop ℕ∞}

theorem GlobalTheory.HermFrame.form_secondFormAdj_mul (hh : (H z).IsHermitian) (hu : IsUnit (subGram (H z)).det) (ξ : E)
    (s : m → ℂ) : form (subGram (H z)) (-(secondFormAdj H z ξ * secondForm H z ξ) *ᵥ s) s =
      -form (quotGram (H z)) (secondForm H z ξ *ᵥ s) (secondForm H z ξ *ᵥ s) := by sorry
