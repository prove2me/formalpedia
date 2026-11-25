-- Prove2me | Theorems.Thm_GlobalTheory_HypOrbitUnique_act_trans
-- name    : GlobalTheory.HypOrbitUnique.act_trans
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:52:26.04055+00:00
-- url     : https://prove2.me/theorems/499532e0-0836-57d6-a1c2-44e0934b9487
-- title:
--   Hyp Orbit Unique: act trans
-- statement:
--   The Hyp Orbit Unique construction uses the act trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HyperboloidInvariantMeasureOrbitRepresentation.lean#L121-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HyperboloidInvariantMeasureOrbitRepresentation.lean#L121-L134

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

theorem GlobalTheory.HypOrbitUnique.act_trans {T' : ℝ} (hT : 0 < T') {x : (Fin k → ℂ) × ℂ} (hx : x ∈ hypS k T') :
    ∃ g : Gp k r, act g (pt k T') = x := by sorry
