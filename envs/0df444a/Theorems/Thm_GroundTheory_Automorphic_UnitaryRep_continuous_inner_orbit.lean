-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_continuous_inner_orbit
-- name    : GroundTheory.Automorphic.UnitaryRep.continuous_inner_orbit
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:33:24.168146+00:00
-- url     : https://prove2.me/theorems/42902780-1dd2-4273-91c8-e1d04172a83e
-- title:
--   Unitary Rep: continuous inner orbit
-- statement:
--   The Unitary Rep construction uses the continuous inner orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/IsInvariantIffCommuteStarProjection.lean#L155-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/IsInvariantIffCommuteStarProjection.lean#L155-L156

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

theorem GroundTheory.Automorphic.UnitaryRep.continuous_inner_orbit (v w : H) : Continuous fun g => ⟪π g v, w⟫_ℂ := by sorry
