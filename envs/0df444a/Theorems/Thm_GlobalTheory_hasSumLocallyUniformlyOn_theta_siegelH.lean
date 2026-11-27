-- Prove2me | Theorems.Thm_GlobalTheory_hasSumLocallyUniformlyOn_theta_siegelH
-- name    : GlobalTheory.hasSumLocallyUniformlyOn_theta_siegelH
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:47:00.536638+00:00
-- url     : https://prove2.me/theorems/97437d6b-cfda-5885-bc69-c00980790c40
-- title:
--   Global Theory: has Sum Locally Uniformly On theta siegel H
-- statement:
--   The Global Theory construction uses the has Sum Locally Uniformly On theta siegel H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L797-L800
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L797-L800

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
open ReciprocityTheory.PTheta

theorem GlobalTheory.hasSumLocallyUniformlyOn_theta_siegelH (a b : ι → ℝ) :
    HasSumLocallyUniformlyOn (fun l (p : (ι → ℂ) × Matrix ι ι ℂ) => thetaTerm a b p.1 p.2 l)
      (fun p => theta a b p.1 p.2) (Set.univ ×ˢ SiegelH ι) := by sorry
