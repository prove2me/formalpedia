-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_nabs_of_valuation_eq_one
-- name    : GlobalTheory.SplitFlip.nabs_of_valuation_eq_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:47.881586+00:00
-- url     : https://prove2.me/theorems/aab538e1-d3d2-466c-99b1-5bfc0012354a
-- title:
--   Split Flip: nabs of valuation eq one
-- statement:
--   The Split Flip construction uses the nabs of valuation eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L34-L39

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

theorem GlobalTheory.SplitFlip.nabs_of_valuation_eq_one {x : kˣ} (hx : valuation k (x : k) = 1) : nabs k x = 1 := by sorry
