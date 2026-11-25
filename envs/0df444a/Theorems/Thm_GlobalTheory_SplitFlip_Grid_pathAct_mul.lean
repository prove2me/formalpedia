-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_Grid_pathAct_mul
-- name    : GlobalTheory.SplitFlip.Grid.pathAct_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:25:24.021828+00:00
-- url     : https://prove2.me/theorems/21c3e886-f497-5abf-bb9a-790b51625515
-- title:
--   Grid: path Act mul
-- statement:
--   The Grid construction uses the path Act mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L999-L1009
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L999-L1009

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

theorem GlobalTheory.SplitFlip.Grid.pathAct_mul (s : Assignment) (γ : List Edge) (g g' : G.VertexGroup) (T : G.Args → ℂ) :
    G.pathAct s γ (g * g') T = G.pathAct s γ g (G.pathAct s γ g' T) := by sorry
