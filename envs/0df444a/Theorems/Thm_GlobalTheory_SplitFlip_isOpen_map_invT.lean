-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_isOpen_map_invT
-- name    : GlobalTheory.SplitFlip.isOpen_map_invT
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:15:47.323849+00:00
-- url     : https://prove2.me/theorems/59b88657-15e6-422b-8b14-bc2671f8b531
-- title:
--   Split Flip: is Open map inv T
-- statement:
--   The Split Flip construction uses the is Open map inv T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L1159-L1167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L1159-L1167

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.SplitFlip.isOpen_map_invT {n : Type*} [Fintype n] [DecidableEq n] {J : Subgroup (GL n k)}
    (ho : IsOpen (J : Set (GL n k))) (hK : J ≤ KO k n) :
    IsOpen (J.map invT : Set (GL n k)) ∧ J.map invT ≤ KO k n := by sorry
