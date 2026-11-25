-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsIrreducible_isEquivalent_of_mem_intertwiners
-- name    : GroundTheory.Automorphic.UnitaryRep.IsIrreducible.isEquivalent_of_mem_intertwiners
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:33:50.570744+00:00
-- url     : https://prove2.me/theorems/cb8207c6-59b8-4a0b-801d-754c48df2ae1
-- title:
--   Is Irreducible: is Equivalent of mem intertwiners
-- statement:
--   The Is Irreducible construction uses the is Equivalent of mem intertwiners property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/ExistsEqAlgebraMapOfIsSelfAdjoint.lean#L129-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/ExistsEqAlgebraMapOfIsSelfAdjoint.lean#L129-L196

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_ExistsEqAlgebraMapOfIsSelfAdjoint
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
open scoped InnerProductSpace ComplexConjugate
open scoped ComplexStarModule
open ContinuousLinearMap Complex
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {π : UnitaryRep G H} {σ : UnitaryRep G K}

theorem GroundTheory.Automorphic.UnitaryRep.IsIrreducible.isEquivalent_of_mem_intertwiners (hπ : π.IsIrreducible)
    (hσ : σ.IsIrreducible) {T : H →L[ℂ] K} (hT : T ∈ π.intertwiners σ) (hT0 : T ≠ 0) :
    π.IsEquivalent σ := by sorry
