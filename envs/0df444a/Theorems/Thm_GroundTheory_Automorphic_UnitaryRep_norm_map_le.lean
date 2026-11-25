-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_norm_map_le
-- name    : GroundTheory.Automorphic.UnitaryRep.norm_map_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:33:41.262799+00:00
-- url     : https://prove2.me/theorems/bf78d470-fa4b-43e3-a09c-d44334399d18
-- title:
--   Unitary Rep: norm map le
-- statement:
--   The Unitary Rep construction uses the norm map le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/IsInvariantIffCommuteStarProjection.lean#L73-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/IsInvariantIffCommuteStarProjection.lean#L73-L74

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

theorem GroundTheory.Automorphic.UnitaryRep.norm_map_le (g : G) : ‖π g‖ ≤ 1 := by sorry
