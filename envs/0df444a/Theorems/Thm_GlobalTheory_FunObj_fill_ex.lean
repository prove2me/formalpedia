-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_fill_ex
-- name    : GlobalTheory.FunObj.fill_ex
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:42:03.991188+00:00
-- url     : https://prove2.me/theorems/3ebc71a6-758c-4026-9337-88e53a24ccbb
-- title:
--   Fun Obj: fill ex
-- statement:
--   The Fun Obj construction uses the fill ex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FlatTensorVacuum.lean#L165-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FlatTensorVacuum.lean#L165-L166

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

theorem GlobalTheory.FunObj.fill_ex (x : ColArgs G) (y : RowArgs G) (e : Vars G) (i : ℕ) : fill hs x y e (.ex i G.m) = (y i)ᵀ := by sorry
