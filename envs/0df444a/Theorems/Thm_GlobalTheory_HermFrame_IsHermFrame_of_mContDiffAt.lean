-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_of_mContDiffAt
-- name    : GlobalTheory.HermFrame.IsHermFrame.of_mContDiffAt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:39:16.341959+00:00
-- url     : https://prove2.me/theorems/6f6d2ff5-d4c0-41e4-bac1-443f1b68fd52
-- title:
--   Is Herm Frame: of m Cont Diff At
-- statement:
--   The Is Herm Frame construction uses the of m Cont Diff At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L330-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L330-L332

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
variable [Fintype n] [DecidableEq n]
variable {U : Set E} {H H' : E → Matrix n n ℂ} {z : E} {j k : WithTop ℕ∞}
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem GlobalTheory.HermFrame.IsHermFrame.of_mContDiffAt (hU : IsOpen U) (h : ∀ z ∈ U, MContDiffAt ∞ H z)
    (h1 : ∀ z ∈ U, (H z).IsHermitian) (h2 : ∀ z ∈ U, IsUnit (H z).det) : IsHermFrame U H := by sorry
