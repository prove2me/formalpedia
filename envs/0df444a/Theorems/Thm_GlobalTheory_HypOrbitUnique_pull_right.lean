-- Prove2me | Theorems.Thm_GlobalTheory_HypOrbitUnique_pull_right
-- name    : GlobalTheory.HypOrbitUnique.pull_right
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:54:44.171264+00:00
-- url     : https://prove2.me/theorems/37f8efb1-242e-415f-b1ca-ce9b186fc68c
-- title:
--   Hyp Orbit Unique: pull right
-- statement:
--   The Hyp Orbit Unique construction uses the pull right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HyperboloidInvariantMeasureOrbitRepresentation.lean#L221-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HyperboloidInvariantMeasureOrbitRepresentation.lean#L221-L228

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

theorem GlobalTheory.HypOrbitUnique.pull_right (ν : Measure (Mt k r)) (hc : ν {x | Matrix.of x ∉ UWb k r} = 0)
    (h : ∀ p ∈ UWb k r, ν.map (rmulM p) = ν) : (pull ν).IsMulRightInvariant := by sorry
