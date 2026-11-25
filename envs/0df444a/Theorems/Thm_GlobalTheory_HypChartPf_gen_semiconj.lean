-- Prove2me | Theorems.Thm_GlobalTheory_HypChartPf_gen_semiconj
-- name    : GlobalTheory.HypChartPf.gen_semiconj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:51:02.472523+00:00
-- url     : https://prove2.me/theorems/d5d82fa8-1523-435c-84bc-2ac4333b6684
-- title:
--   Hyp Chart Pf: gen semiconj
-- statement:
--   The Hyp Chart Pf construction uses the gen semiconj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HyperboloidChartMeasureFormula.lean#L115-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HyperboloidChartMeasureFormula.lean#L115-L121

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

theorem GlobalTheory.HypChartPf.gen_semiconj (k r : ℕ) (q : TrE k) :
    SemiconjBy (Matrix.diagonal (sgn k r)) (-opGen k r q) (opGen k r q)ᴴ := by sorry
