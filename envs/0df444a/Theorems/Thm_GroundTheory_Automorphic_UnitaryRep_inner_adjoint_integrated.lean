-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_inner_adjoint_integrated
-- name    : GroundTheory.Automorphic.UnitaryRep.inner_adjoint_integrated
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:33:36.831089+00:00
-- url     : https://prove2.me/theorems/df973617-8640-4e4d-aee8-d7438517d789
-- title:
--   Unitary Rep: inner adjoint integrated
-- statement:
--   The Unitary Rep construction uses the inner adjoint integrated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/Integrated.lean#L164-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/Integrated.lean#L164-L168

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_Integrated
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
open MeasureTheory Filter
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (π : UnitaryRep G H) (μ : Measure G)

theorem GroundTheory.Automorphic.UnitaryRep.inner_adjoint_integrated (f : G →₁[μ] ℂ) (w v : H) :
    ⟪w, adjoint (π.integrated μ f) v⟫_ℂ = ∫ g, conj (f g) * ⟪w, π g⁻¹ v⟫_ℂ ∂μ := by sorry
