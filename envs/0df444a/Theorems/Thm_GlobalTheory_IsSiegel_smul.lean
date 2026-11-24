-- Prove2me | Theorems.Thm_GlobalTheory_IsSiegel_smul
-- name    : GlobalTheory.IsSiegel.smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:49.656693+00:00
-- url     : https://prove2.me/theorems/523fcbb3-264b-44b7-9751-8663d414c2a9
-- title:
--   Is Siegel: smul
-- statement:
--   The Is Siegel construction uses the smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L87-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L87-L92

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

theorem GlobalTheory.IsSiegel.smul {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω) {q : ℝ} (hq : 0 < q) :
    IsSiegel ((q : ℂ) • Ω) := by sorry
