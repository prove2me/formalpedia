-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_orthogonalProjection_mem_intertwiners
-- name    : GroundTheory.Automorphic.UnitaryRep.orthogonalProjection_mem_intertwiners
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:05:09.643531+00:00
-- url     : https://prove2.me/theorems/fca15d69-e405-4aa0-b624-e00b37d3311a
-- title:
--   Unitary Rep: orthogonal Projection mem intertwiners
-- statement:
--   The Unitary Rep construction uses the orthogonal Projection mem intertwiners property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceFormulaMultiplicity.lean#L20-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceFormulaMultiplicity.lean#L20-L29

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

theorem GroundTheory.Automorphic.UnitaryRep.orthogonalProjection_mem_intertwiners (j : J) :
    ((V j).orthogonalProjectionOnto : H →L[ℂ] V j) ∈ π.intertwiners (π.restrict (V j) (hinv j)) := by sorry
