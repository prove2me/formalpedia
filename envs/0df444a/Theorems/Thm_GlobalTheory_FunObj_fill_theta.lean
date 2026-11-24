-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_fill_theta
-- name    : GlobalTheory.FunObj.fill_theta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:52:31.0436+00:00
-- url     : https://prove2.me/theorems/91138871-0931-49a4-99cd-71e66014b2f6
-- title:
--   Fun Obj: fill theta
-- statement:
--   The Fun Obj construction uses the fill theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FlatTensorVacuum.lean#L162-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FlatTensorVacuum.lean#L162-L163

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

theorem GlobalTheory.FunObj.fill_theta (x : ColArgs G) (y : RowArgs G) (e : Vars G) (j : ℕ) :
    fill hs x y e (.theta G.m j) = (downMap hs x e j)ᵀ := by sorry
