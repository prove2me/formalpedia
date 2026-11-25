-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_directSum_apply
-- name    : GroundTheory.Automorphic.UnitaryRep.directSum_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:14:42.415626+00:00
-- url     : https://prove2.me/theorems/72ec83e1-4bdc-4ad6-8a92-a8b7a4bb2997
-- title:
--   Unitary Rep: direct Sum apply
-- statement:
--   The Unitary Rep construction uses the direct Sum apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/DirectSum.lean#L77-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/DirectSum.lean#L77-L78

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

theorem GroundTheory.Automorphic.UnitaryRep.directSum_apply (g : G) (x : lp E 2) (i : ι) :
    directSum ρ g x i = ρ i g (x i) := by sorry

attribute [defeq] GroundTheory.Automorphic.UnitaryRep.directSum_apply
