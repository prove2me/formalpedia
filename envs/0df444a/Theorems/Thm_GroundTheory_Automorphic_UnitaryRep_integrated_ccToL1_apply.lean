-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_integrated_ccToL1_apply
-- name    : GroundTheory.Automorphic.UnitaryRep.integrated_ccToL1_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:30:29.225018+00:00
-- url     : https://prove2.me/theorems/d2cf406c-9b51-46ca-8135-4afff81d94c5
-- title:
--   Unitary Rep: integrated cc To L1 apply
-- statement:
--   The Unitary Rep construction uses the integrated cc To L1 apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L22-L25

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.UnitaryRep
open MeasureTheory Filter Topology Module End
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
noncomputable section
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem GroundTheory.Automorphic.UnitaryRep.integrated_ccToL1_apply (π : UnitaryRep G H) (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (f : CompactlySupportedContinuousMap G ℂ) (v : H) :
    π.integrated μ (ccToL1 μ f) v = ∫ g, f g • π g v ∂μ := by sorry
