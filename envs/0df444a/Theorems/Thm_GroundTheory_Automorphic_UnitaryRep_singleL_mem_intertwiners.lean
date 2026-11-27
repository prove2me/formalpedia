-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_singleL_mem_intertwiners
-- name    : GroundTheory.Automorphic.UnitaryRep.singleL_mem_intertwiners
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:54:20.116527+00:00
-- url     : https://prove2.me/theorems/10cffdee-e952-4e5f-89b7-1e781d9c9881
-- title:
--   Unitary Rep: single L mem intertwiners
-- statement:
--   The Unitary Rep construction uses the single L mem intertwiners property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/DirectSum.lean#L88-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/DirectSum.lean#L88-L96

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_DirectSum
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
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
variable (ρ : ∀ i, UnitaryRep G (E i))

theorem GroundTheory.Automorphic.UnitaryRep.singleL_mem_intertwiners [DecidableEq ι] (i : ι) :
    singleL i ∈ (ρ i).intertwiners (directSum ρ) := by sorry
