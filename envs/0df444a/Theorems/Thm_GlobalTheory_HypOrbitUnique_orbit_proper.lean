-- Prove2me | Theorems.Thm_GlobalTheory_HypOrbitUnique_orbit_proper
-- name    : GlobalTheory.HypOrbitUnique.orbit_proper
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:52:58.527011+00:00
-- url     : https://prove2.me/theorems/d27bfd23-2a7d-4ab1-b144-3af6c5774ac8
-- title:
--   Hyp Orbit Unique: orbit proper
-- statement:
--   The Hyp Orbit Unique construction uses the orbit proper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HyperboloidInvariantMeasureOrbitRepresentation.lean#L176-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HyperboloidInvariantMeasureOrbitRepresentation.lean#L176-L219

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HyperboloidInvariantMeasureOrbitRepresentation
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
open GlobalTheory GlobalTheory.HypOrbitUnique
open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.HU PI.RhsWLim.W.MB
variable {k r : ℕ}

theorem GlobalTheory.HypOrbitUnique.orbit_proper {T' : ℝ} (hT : 0 < T') (R : ℝ) :
    ∃ K : Set (Gp k r), IsCompact K ∧ ∀ g, act g (pt k T') ∈ Metric.closedBall 0 R → g ∈ K := by sorry
