-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsIrreducible_spectrum_subsingleton
-- name    : GroundTheory.Automorphic.UnitaryRep.IsIrreducible.spectrum_subsingleton
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:33:52.07794+00:00
-- url     : https://prove2.me/theorems/1004ee22-e4d2-4a1f-b5f9-a4ce82d8f884
-- title:
--   Is Irreducible: spectrum subsingleton
-- statement:
--   The Is Irreducible construction uses the spectrum subsingleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/ExistsEqAlgebraMapOfIsSelfAdjoint.lean#L23-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/ExistsEqAlgebraMapOfIsSelfAdjoint.lean#L23-L76

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

theorem GroundTheory.Automorphic.UnitaryRep.IsIrreducible.spectrum_subsingleton (hπ : π.IsIrreducible) {A : H →L[ℂ] H}
    (hA : A ∈ π.intertwiners π) (hsa : IsSelfAdjoint A) : (spectrum ℝ A).Subsingleton := by sorry
