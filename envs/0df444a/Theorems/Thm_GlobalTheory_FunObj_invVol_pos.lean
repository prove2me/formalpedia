-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_invVol_pos
-- name    : GlobalTheory.FunObj.invVol_pos
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:41:08.928864+00:00
-- url     : https://prove2.me/theorems/6ab8e285-29a7-4b42-bc7b-a3d49ba1119b
-- title:
--   Fun Obj: inv Vol pos
-- statement:
--   The Fun Obj construction uses the inv Vol pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FlatTensorVacuum.lean#L99-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FlatTensorVacuum.lean#L99-L102

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

theorem GlobalTheory.FunObj.invVol_pos {C : Subgroup (GL (n ⊕ Fin c) k)} (ho : IsOpen (C : Set (GL (n ⊕ Fin c) k)))
    (hc : IsCompact (C : Set (GL (n ⊕ Fin c) k))) : 0 < invVol C := by sorry
