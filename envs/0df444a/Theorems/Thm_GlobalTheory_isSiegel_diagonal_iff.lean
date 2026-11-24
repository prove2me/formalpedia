-- Prove2me | Theorems.Thm_GlobalTheory_isSiegel_diagonal_iff
-- name    : GlobalTheory.isSiegel_diagonal_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:19.970522+00:00
-- url     : https://prove2.me/theorems/4c134b73-893e-4c87-9c40-395fdb88db98
-- title:
--   Global Theory: is Siegel diagonal iff
-- statement:
--   The Global Theory construction uses the is Siegel diagonal iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L65-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L65-L70

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

theorem GlobalTheory.isSiegel_diagonal_iff [DecidableEq ι] {τ : ι → ℂ} :
    IsSiegel (diagonal τ) ↔ ∀ i, 0 < (τ i).im := by sorry
