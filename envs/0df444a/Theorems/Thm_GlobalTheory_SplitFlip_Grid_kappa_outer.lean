-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_Grid_kappa_outer
-- name    : GlobalTheory.SplitFlip.Grid.kappa_outer
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:26:10.726943+00:00
-- url     : https://prove2.me/theorems/0916f436-a739-4d1c-9e8d-2139cf3cd27a
-- title:
--   Grid: kappa outer
-- statement:
--   The Grid construction uses the kappa outer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L962-L964
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L962-L964

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
open GlobalTheory.SplitFlip.Grid
variable (G : Grid k)
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.SplitFlip.Grid.kappa_outer (i j : ℕ) :
    G.kappa (.theta (i + 1) j) (i + 1, j + 1) / G.kappa (.ex i (j + 1)) (i + 1, j + 1) = G.nu i j := by sorry
