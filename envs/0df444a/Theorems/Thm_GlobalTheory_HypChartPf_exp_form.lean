-- Prove2me | Theorems.Thm_GlobalTheory_HypChartPf_exp_form
-- name    : GlobalTheory.HypChartPf.exp_form
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:50:37.470433+00:00
-- url     : https://prove2.me/theorems/820603b1-b6b8-5376-bac5-e43936030f69
-- title:
--   Hyp Chart Pf: exp form
-- statement:
--   The Hyp Chart Pf construction uses the exp form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HyperboloidChartMeasureFormula.lean#L169-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HyperboloidChartMeasureFormula.lean#L169-L182

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

theorem GlobalTheory.HypChartPf.exp_form (k r : ℕ) (q : TrE k) :
    (NormedSpace.exp (opGen k r q))ᴴ * Matrix.diagonal (sgn k r) * NormedSpace.exp (opGen k r q) =
      Matrix.diagonal (sgn k r) := by sorry
