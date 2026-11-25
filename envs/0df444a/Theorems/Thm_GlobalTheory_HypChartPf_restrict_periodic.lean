-- Prove2me | Theorems.Thm_GlobalTheory_HypChartPf_restrict_periodic
-- name    : GlobalTheory.HypChartPf.restrict_periodic
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:50:43.299401+00:00
-- url     : https://prove2.me/theorems/1f76d53c-bf51-5f9f-8031-272c1cfb718a
-- title:
--   Hyp Chart Pf: restrict periodic
-- statement:
--   The Hyp Chart Pf construction uses the restrict periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HyperboloidChartMeasureFormula.lean#L42-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HyperboloidChartMeasureFormula.lean#L42-L69

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushQ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HyperboloidChartMeasureFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.HypChartPf
open PI.RhsWLim PI.RhsWLim.W

theorem GlobalTheory.HypChartPf.restrict_periodic (A : Set ℝ) (hA : MeasurableSet A) (hp : ∀ x, x + 2 * Real.pi ∈ A ↔ x ∈ A) :
    volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)) A = volume.restrict (Set.Ioc (-Real.pi) Real.pi) A := by sorry
