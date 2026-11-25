-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_adj_curv
-- name    : GlobalTheory.HermFrame.adj_curv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:38:03.400295+00:00
-- url     : https://prove2.me/theorems/5ae58ad1-f8ab-4b8c-8ef2-3f05642016b5
-- title:
--   Herm Frame: adj curv
-- statement:
--   The Herm Frame construction uses the adj curv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L438-L447
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L438-L447

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

theorem GlobalTheory.HermFrame.adj_curv (h : MContDiffAt 2 H z) (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian)
    (hu : IsUnit (H z).det) (ξ η : E) : adj (H z) (H z) (curv H z ξ η) = curv H z η ξ := by sorry
