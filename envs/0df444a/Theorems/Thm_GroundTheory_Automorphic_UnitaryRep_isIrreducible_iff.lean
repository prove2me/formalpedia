-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_isIrreducible_iff
-- name    : GroundTheory.Automorphic.UnitaryRep.isIrreducible_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:15:54.405326+00:00
-- url     : https://prove2.me/theorems/aa9634ac-6df2-40fe-8282-d00dca75eaba
-- title:
--   Unitary Rep: is Irreducible iff
-- statement:
--   The Unitary Rep construction uses the is Irreducible iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/ExistsEqAlgebraMapOfIsSelfAdjoint.lean#L107-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/ExistsEqAlgebraMapOfIsSelfAdjoint.lean#L107-L127

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_ExistsEqAlgebraMapOfIsSelfAdjoint
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_isIrreducible_iff

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

theorem GroundTheory.Automorphic.UnitaryRep.isIrreducible_iff :
    π.IsIrreducible ↔
      Nontrivial H ∧ ∀ T ∈ π.intertwiners π, ∃ c : ℂ, T = c • (1 : H →L[ℂ] H) := by sorry
