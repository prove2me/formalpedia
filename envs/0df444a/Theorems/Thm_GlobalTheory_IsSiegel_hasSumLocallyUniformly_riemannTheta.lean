-- Prove2me | Theorems.Thm_GlobalTheory_IsSiegel_hasSumLocallyUniformly_riemannTheta
-- name    : GlobalTheory.IsSiegel.hasSumLocallyUniformly_riemannTheta
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:11:36.726018+00:00
-- url     : https://prove2.me/theorems/a563ed0b-6c1c-45b6-94fb-2e6a1faf1011
-- title:
--   Is Siegel: has Sum Locally Uniformly riemann Theta
-- statement:
--   The Is Siegel construction uses the has Sum Locally Uniformly riemann Theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L379-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L379-L384

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

theorem GlobalTheory.IsSiegel.hasSumLocallyUniformly_riemannTheta {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) :
    HasSumLocallyUniformly (fun n v => riemannThetaTerm a b Ω v n) (riemannTheta a b Ω) := by sorry
