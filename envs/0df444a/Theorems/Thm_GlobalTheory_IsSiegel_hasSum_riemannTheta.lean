-- Prove2me | Theorems.Thm_GlobalTheory_IsSiegel_hasSum_riemannTheta
-- name    : GlobalTheory.IsSiegel.hasSum_riemannTheta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:00.912745+00:00
-- url     : https://prove2.me/theorems/85640e17-546b-4916-86ca-cb4e47700cdf
-- title:
--   Is Siegel: has Sum riemann Theta
-- statement:
--   The Is Siegel construction uses the has Sum riemann Theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L355-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L355-L357

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
variable [Fintype ι] [Fintype κ]

theorem GlobalTheory.IsSiegel.hasSum_riemannTheta {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) (v : ι → ℂ) : HasSum (riemannThetaTerm a b Ω v) (riemannTheta a b Ω v) := by sorry
