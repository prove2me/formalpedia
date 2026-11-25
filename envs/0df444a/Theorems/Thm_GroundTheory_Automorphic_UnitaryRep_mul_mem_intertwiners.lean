-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_mul_mem_intertwiners
-- name    : GroundTheory.Automorphic.UnitaryRep.mul_mem_intertwiners
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:53:58.176813+00:00
-- url     : https://prove2.me/theorems/ed80826c-7dd1-4c02-aa53-b270e8a3e0e1
-- title:
--   Unitary Rep: mul mem intertwiners
-- statement:
--   The Unitary Rep construction uses the mul mem intertwiners property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/IsInvariantIffCommuteStarProjection.lean#L225-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/IsInvariantIffCommuteStarProjection.lean#L225-L226

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

theorem GroundTheory.Automorphic.UnitaryRep.mul_mem_intertwiners {S T : H →L[ℂ] H} (hS : S ∈ π.intertwiners π)
    (hT : T ∈ π.intertwiners π) : S * T ∈ π.intertwiners π := by sorry
