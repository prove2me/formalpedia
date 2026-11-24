-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_stepPt_eq
-- name    : GlobalTheory.FunObj.stepPt_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:17.722014+00:00
-- url     : https://prove2.me/theorems/4fcdecd3-0c8a-4b6c-bd9b-ae06a463a3cf
-- title:
--   Fun Obj: step Pt eq
-- statement:
--   The Fun Obj construction uses the step Pt eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FlatTensorVacuum.lean#L76-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FlatTensorVacuum.lean#L76-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (c : ℕ)
variable {k n c}
variable {n' : Type*} [Fintype n'] [DecidableEq n']
omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem GlobalTheory.FunObj.stepPt_eq (x₀ : Matrix n n' k) (e : StepVar n c n' → k) : stepPt x₀ e =
    affPt (c / 2 + 1) x₀ (fun rs => e ⟨rs.1, Or.inl rs.2⟩) + keptPt fun rs => e ⟨rs.1, Or.inr rs.2⟩ := by sorry
