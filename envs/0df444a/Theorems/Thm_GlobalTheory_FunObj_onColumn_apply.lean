-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_onColumn_apply
-- name    : GlobalTheory.FunObj.onColumn_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:01:59.401622+00:00
-- url     : https://prove2.me/theorems/9dbdc619-28e2-4381-80ff-0e349840feec
-- title:
--   Fun Obj: on Column apply
-- statement:
--   The Fun Obj construction uses the on Column apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FlatTensorVacuum.lean#L193-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FlatTensorVacuum.lean#L193-L193

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

theorem GlobalTheory.FunObj.onColumn_apply (h : ∀ j : ℕ, GL (Fin (G.rank (G.m, j))) k) (j : ℕ) : onColumn h (G.m, j) = h j := by sorry
