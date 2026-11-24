-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_mul_mul_mem_matLat_iff
-- name    : GlobalTheory.SplitFlip.mul_mul_mem_matLat_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:20:40.783486+00:00
-- url     : https://prove2.me/theorems/ab568bda-6de0-4254-8eba-b55e12aad348
-- title:
--   Split Flip: mul mul mem mat Lat iff
-- statement:
--   The Split Flip construction uses the mul mul mem mat Lat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L1100-L1110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L1100-L1110

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

theorem GlobalTheory.SplitFlip.mul_mul_mem_matLat_iff {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {g : GL m k} {h : GL n k} (hg : g ∈ KO k m) (hh : h ∈ KO k n) (X : Matrix m n k) :
    g.val * X * h.val ∈ matLat m (stdLat k n) ↔ X ∈ matLat m (stdLat k n) := by sorry
