-- Prove2me | Theorems.Thm_GlobalTheory_HypOrbitUnique_fubini_identity
-- name    : GlobalTheory.HypOrbitUnique.fubini_identity
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:53:52.623481+00:00
-- url     : https://prove2.me/theorems/20e72484-a0d3-458d-a61b-1e12b6019d53
-- title:
--   Hyp Orbit Unique: fubini identity
-- statement:
--   The Hyp Orbit Unique construction uses the fubini identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HyperboloidInvariantMeasureOrbitRepresentation.lean#L16-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HyperboloidInvariantMeasureOrbitRepresentation.lean#L16-L59

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

theorem GlobalTheory.HypOrbitUnique.fubini_identity {G X : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
    [MeasurableSpace X] (act : G → X → X) (hm : Measurable (Function.uncurry act))
    (hmul : ∀ g g' x, act (g * g') x = act g (act g' x)) (hone : ∀ x, act 1 x = x)
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (Q : Measure X) [SFinite Q] (hQ : ∀ g, Q.map (act g) = Q) (x₀ : X)
    (htr : ∀ᵐ x ∂Q, ∃ g, act g x₀ = x) {f h : X → ℝ≥0∞} (hf : Measurable f) (hh : Measurable h) :
    (∫⁻ g, f (act g x₀) ∂μ) * ∫⁻ x, h x ∂Q = (∫⁻ x, f x ∂Q) * ∫⁻ g, h (act g⁻¹ x₀) ∂μ := by sorry
