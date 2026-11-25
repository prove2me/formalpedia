-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_orthogonalProjection_coe_eq_zero
-- name    : GroundTheory.Automorphic.UnitaryRep.orthogonalProjection_coe_eq_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:04:07.9143+00:00
-- url     : https://prove2.me/theorems/3c84d657-3abb-4b24-9473-5e0db84c9229
-- title:
--   Unitary Rep: orthogonal Projection coe eq zero
-- statement:
--   The Unitary Rep construction uses the orthogonal Projection coe eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceFormulaMultiplicity.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceFormulaMultiplicity.lean#L35-L39

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

theorem GroundTheory.Automorphic.UnitaryRep.orthogonalProjection_coe_eq_zero {i j : J} (hij : i ≠ j) (v : V j) :
    (V i).orthogonalProjectionOnto (v : H) = 0 := by sorry
