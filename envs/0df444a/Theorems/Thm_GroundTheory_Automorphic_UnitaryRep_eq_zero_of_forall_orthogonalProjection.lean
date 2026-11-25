-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_eq_zero_of_forall_orthogonalProjection
-- name    : GroundTheory.Automorphic.UnitaryRep.eq_zero_of_forall_orthogonalProjection
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:04:02.347971+00:00
-- url     : https://prove2.me/theorems/64fee721-34c5-48a6-bdc8-966eeeedbbe5
-- title:
--   Unitary Rep: eq zero of forall orthogonal Projection
-- statement:
--   The Unitary Rep construction uses the eq zero of forall orthogonal Projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceFormulaMultiplicity.lean#L43-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceFormulaMultiplicity.lean#L43-L55

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaSpectral
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_ExistsEqAlgebraMapOfIsSelfAdjoint
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaMultiplicity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ContinuousLinearMap
open scoped InnerProductSpace
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.UnitaryRep
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {π : UnitaryRep G H} {J : Type*} {V : J → Submodule ℂ H} [∀ j, CompleteSpace (V j)]
  (hinv : ∀ j, π.IsInvariant (V j))
variable (hsum : IsHilbertSum ℂ (fun j => V j) fun j => (V j).subtypeₗᵢ)
include hsum

theorem GroundTheory.Automorphic.UnitaryRep.eq_zero_of_forall_orthogonalProjection {x : H}
    (hx : ∀ j, (V j).orthogonalProjectionOnto x = 0) : x = 0 := by sorry
