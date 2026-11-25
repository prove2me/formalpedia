-- Prove2me | Theorems.Thm_GlobalTheory_HypOrbitUnique_opCo_opVec
-- name    : GlobalTheory.HypOrbitUnique.opCo_opVec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:59:17.077743+00:00
-- url     : https://prove2.me/theorems/e61bdf7c-baa7-4982-a30b-b3a766ad64be
-- title:
--   Hyp Orbit Unique: op Co op Vec
-- statement:
--   The Hyp Orbit Unique construction uses the op Co op Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HyperboloidInvariantMeasureOrbitRepresentation.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HyperboloidInvariantMeasureOrbitRepresentation.lean#L78-L81

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

theorem GlobalTheory.HypOrbitUnique.opCo_opVec (p : (Fin k → ℂ) × ℂ) : opCo k r (opVec k r p) = p := by sorry
