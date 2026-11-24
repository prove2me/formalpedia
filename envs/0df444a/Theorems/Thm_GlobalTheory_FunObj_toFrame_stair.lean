-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_toFrame_stair
-- name    : GlobalTheory.FunObj.toFrame_stair
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:43:58.571531+00:00
-- url     : https://prove2.me/theorems/49a1109e-9723-4e8d-8161-e851ae13ec6a
-- title:
--   Fun Obj: to Frame stair
-- statement:
--   The Fun Obj construction uses the to Frame stair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FlatTensorVacuum.lean#L216-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FlatTensorVacuum.lean#L216-L226

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
variable {k : Type*} [Field k] (G : Grid k)
variable {G}
variable (hs : 1 ≤ G.s)
variable {hs}

theorem GlobalTheory.FunObj.toFrame_stair (ϖ : kˣ) (e : ℕ) {j : ℕ} (hj : j < G.m) : toFrame hs hj (stair G ϖ e j) =
    diagGL (Sum.elim (fun _ => 1) fun p => ϖ ^ (e * (p.val + 1))) := by sorry
