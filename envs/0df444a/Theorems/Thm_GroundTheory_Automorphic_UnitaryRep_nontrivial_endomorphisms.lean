-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_nontrivial_endomorphisms
-- name    : GroundTheory.Automorphic.UnitaryRep.nontrivial_endomorphisms
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:34.027446+00:00
-- url     : https://prove2.me/theorems/17a9154c-5c63-498c-89a3-2adecd33c575
-- title:
--   Unitary Rep: nontrivial endomorphisms
-- statement:
--   The Unitary Rep construction uses the nontrivial endomorphisms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/ExistsEqAlgebraMapOfIsSelfAdjoint.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/ExistsEqAlgebraMapOfIsSelfAdjoint.lean#L19-L21

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
omit [CompleteSpace H]

theorem GroundTheory.Automorphic.UnitaryRep.nontrivial_endomorphisms [Nontrivial H] : Nontrivial (H →L[ℂ] H) := by sorry
