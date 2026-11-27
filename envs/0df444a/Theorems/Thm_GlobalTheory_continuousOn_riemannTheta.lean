-- Prove2me | Theorems.Thm_GlobalTheory_continuousOn_riemannTheta
-- name    : GlobalTheory.continuousOn_riemannTheta
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:45:18.82551+00:00
-- url     : https://prove2.me/theorems/6478284d-f190-48aa-b651-5101e41fa242
-- title:
--   Global Theory: continuous On riemann Theta
-- statement:
--   The Global Theory construction uses the continuous On riemann Theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L393-L398
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L393-L398

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

theorem GlobalTheory.continuousOn_riemannTheta (a b : ι → ℝ) :
    ContinuousOn (fun p : (ι → ℂ) × Matrix ι ι ℂ => riemannTheta a b p.2 p.1)
      (Set.univ ×ˢ ReciprocityTheory.PTheta.SiegelH ι) := by sorry
