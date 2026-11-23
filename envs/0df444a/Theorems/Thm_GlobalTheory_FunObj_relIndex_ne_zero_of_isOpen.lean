-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_relIndex_ne_zero_of_isOpen
-- name    : GlobalTheory.FunObj.relIndex_ne_zero_of_isOpen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:40.742301+00:00
-- url     : https://prove2.me/theorems/5d21aabf-b055-4383-ab60-3acc5517c9da
-- title:
--   Fun Obj: rel Index ne zero of is Open
-- statement:
--   The Fun Obj construction uses the rel Index ne zero of is Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FlatTensorVacuum.lean#L93-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FlatTensorVacuum.lean#L93-L97

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
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.FunObj.relIndex_ne_zero_of_isOpen {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {U K H : Subgroup G} (hU : IsOpen (U : Set G)) (hK : IsCompact (K : Set G)) (hH : H ≤ K) : U.relIndex H ≠ 0 := by sorry
