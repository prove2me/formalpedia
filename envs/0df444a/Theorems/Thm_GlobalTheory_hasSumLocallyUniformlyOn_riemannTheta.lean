-- Prove2me | Theorems.Thm_GlobalTheory_hasSumLocallyUniformlyOn_riemannTheta
-- name    : GlobalTheory.hasSumLocallyUniformlyOn_riemannTheta
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:15.279332+00:00
-- url     : https://prove2.me/theorems/77e69f37-b7fa-4494-80bf-8d5a74af8246
-- title:
--   Global Theory: has Sum Locally Uniformly On riemann Theta
-- statement:
--   The Global Theory construction uses the has Sum Locally Uniformly On riemann Theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L369-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L369-L377

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

theorem GlobalTheory.hasSumLocallyUniformlyOn_riemannTheta (a b : ι → ℝ) :
    HasSumLocallyUniformlyOn
      (fun n (p : (ι → ℂ) × Matrix ι ι ℂ) => riemannThetaTerm a b p.2 p.1 n)
      (fun p => riemannTheta a b p.2 p.1) (Set.univ ×ˢ ReciprocityTheory.PTheta.SiegelH ι) := by sorry
