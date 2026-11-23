-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_adjoint_mem_intertwiners
-- name    : GroundTheory.Automorphic.UnitaryRep.adjoint_mem_intertwiners
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:37.689797+00:00
-- url     : https://prove2.me/theorems/613e1ea8-83d5-4888-a6fa-ae6ccc8573b7
-- title:
--   Unitary Rep: adjoint mem intertwiners
-- statement:
--   The Unitary Rep construction uses the adjoint mem intertwiners property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/IsInvariantIffCommuteStarProjection.lean#L228-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/IsInvariantIffCommuteStarProjection.lean#L228-L233

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

theorem GroundTheory.Automorphic.UnitaryRep.adjoint_mem_intertwiners {T : H →L[ℂ] K} (hT : T ∈ π.intertwiners σ) :
    adjoint T ∈ σ.intertwiners π := by sorry
