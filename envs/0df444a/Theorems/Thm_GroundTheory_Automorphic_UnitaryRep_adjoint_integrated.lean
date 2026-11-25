-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_adjoint_integrated
-- name    : GroundTheory.Automorphic.UnitaryRep.adjoint_integrated
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:53:47.538844+00:00
-- url     : https://prove2.me/theorems/47912c69-ff92-4ef7-919e-885e42eae0f7
-- title:
--   Unitary Rep: adjoint integrated
-- statement:
--   The Unitary Rep construction uses the adjoint integrated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/Integrated.lean#L206-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/Integrated.lean#L206-L213

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
variable [IsTopologicalGroup G] [BorelSpace G]

theorem GroundTheory.Automorphic.UnitaryRep.adjoint_integrated [μ.IsInvInvariant] (f : G →₁[μ] ℂ) :
    adjoint (π.integrated μ f) = π.integrated μ (involution μ f) := by sorry
