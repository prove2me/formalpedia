-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_Kept_not_free
-- name    : GlobalTheory.FunObj.Kept.not_free
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:59:08.90312+00:00
-- url     : https://prove2.me/theorems/d7709c3c-ad06-4242-a55a-58922bc44539
-- title:
--   Kept: not free
-- statement:
--   The Kept construction uses the not free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FlatTensorVacuum.lean#L57-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FlatTensorVacuum.lean#L57-L58

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

theorem GlobalTheory.FunObj.Kept.not_free {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} (h : Kept rs) : ¬ Free (c / 2 + 1) rs := by sorry
