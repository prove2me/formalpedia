-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_singleL_apply
-- name    : GroundTheory.Automorphic.UnitaryRep.singleL_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:15:00.314324+00:00
-- url     : https://prove2.me/theorems/7982f313-2a04-42ce-93dd-e51d1462f4d0
-- title:
--   Unitary Rep: single L apply
-- statement:
--   The Unitary Rep construction uses the single L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/DirectSum.lean#L86-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/DirectSum.lean#L86-L86

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
omit [∀ i, CompleteSpace (E i)]

theorem GroundTheory.Automorphic.UnitaryRep.singleL_apply [DecidableEq ι] (i : ι) (a : E i) : singleL i a = lp.single 2 i a := by sorry
