-- Prove2me | Theorems.Thm_GlobalTheory_isSiegel_fromBlocks_iff
-- name    : GlobalTheory.isSiegel_fromBlocks_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:48:08.661124+00:00
-- url     : https://prove2.me/theorems/e18509a9-afa6-5db5-9266-9eeb026abdb9
-- title:
--   Global Theory: is Siegel from Blocks iff
-- statement:
--   The Global Theory construction uses the is Siegel from Blocks iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L102-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L102-L124

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι κ : Type*}

theorem GlobalTheory.isSiegel_fromBlocks_iff [Finite ι] [Finite κ] {Ω₁ : Matrix ι ι ℂ} {Ω₂ : Matrix κ κ ℂ} :
    IsSiegel (fromBlocks Ω₁ 0 0 Ω₂) ↔ IsSiegel Ω₁ ∧ IsSiegel Ω₂ := by sorry
