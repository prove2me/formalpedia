-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_curv_submatrix_equiv
-- name    : GlobalTheory.HermFrame.curv_submatrix_equiv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:07:03.820798+00:00
-- url     : https://prove2.me/theorems/a6fe5784-68c7-469a-9193-3bd6aecaf86c
-- title:
--   Herm Frame: curv submatrix equiv
-- statement:
--   The Herm Frame construction uses the curv submatrix equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L874-L877
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L874-L877

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

theorem GlobalTheory.HermFrame.curv_submatrix_equiv [Fintype n] [DecidableEq n] (K : E → Matrix n n ℂ) (e : m ≃ n)
    (z ξ η : E) : curv (fun x => (K x).submatrix e e) z ξ η = (curv K z ξ η).submatrix e e := by sorry
