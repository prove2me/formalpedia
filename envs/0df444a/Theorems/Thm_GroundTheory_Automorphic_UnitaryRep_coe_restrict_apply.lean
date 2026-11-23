-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
-- name    : GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:46.825939+00:00
-- url     : https://prove2.me/theorems/f75f40c6-24f4-4125-80a8-ef8265e50a76
-- title:
--   Unitary Rep: coe restrict apply
-- statement:
--   The Unitary Rep construction uses the coe restrict apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/IsInvariantIffCommuteStarProjection.lean#L354-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/IsInvariantIffCommuteStarProjection.lean#L354-L355

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
variable (π) (V : Submodule ℂ H) [CompleteSpace V] (hV : π.IsInvariant V)

theorem GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply (g : G) (v : V) :
    ((π.restrict V hV g v : V) : H) = π g v := by sorry

attribute [defeq] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
