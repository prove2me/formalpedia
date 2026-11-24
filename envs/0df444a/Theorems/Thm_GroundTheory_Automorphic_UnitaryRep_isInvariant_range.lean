-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_isInvariant_range
-- name    : GroundTheory.Automorphic.UnitaryRep.isInvariant_range
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:33:41.966545+00:00
-- url     : https://prove2.me/theorems/c75bff79-daa3-4656-b869-0eeab338f3f7
-- title:
--   Unitary Rep: is Invariant range
-- statement:
--   The Unitary Rep construction uses the is Invariant range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/IsInvariantIffCommuteStarProjection.lean#L248-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/IsInvariantIffCommuteStarProjection.lean#L248-L251

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap Filter Topology
open GroundTheory.Automorphic.UnitaryRep
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable (π : UnitaryRep G H)
variable {π}
variable {σ : UnitaryRep G K} {τ : UnitaryRep G L}

theorem GroundTheory.Automorphic.UnitaryRep.isInvariant_range {T : H →L[ℂ] K} (hT : T ∈ π.intertwiners σ) :
    σ.IsInvariant (LinearMap.range (T : H →ₗ[ℂ] K)) := by sorry
