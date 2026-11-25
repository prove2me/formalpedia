-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_isIrreducible_iff
-- name    : GroundTheory.Automorphic.UnitaryRep.IsEquivalent.isIrreducible_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:26.044806+00:00
-- url     : https://prove2.me/theorems/2db081b1-6610-4c76-a846-0ee5d065850b
-- title:
--   Is Equivalent: is Irreducible iff
-- statement:
--   The Is Equivalent construction uses the is Irreducible iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/IsInvariantIffCommuteStarProjection.lean#L329-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/IsInvariantIffCommuteStarProjection.lean#L329-L331

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

theorem GroundTheory.Automorphic.UnitaryRep.IsEquivalent.isIrreducible_iff (h : π.IsEquivalent σ) :
    π.IsIrreducible ↔ σ.IsIrreducible := by sorry
