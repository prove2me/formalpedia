-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_isEquivalent_directSum_of_isHilbertSum
-- name    : GroundTheory.Automorphic.UnitaryRep.isEquivalent_directSum_of_isHilbertSum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:53:45.395722+00:00
-- url     : https://prove2.me/theorems/f6836030-7f12-54f3-b0bd-6a4170a52e07
-- title:
--   Unitary Rep: is Equivalent direct Sum of is Hilbert Sum
-- statement:
--   The Unitary Rep construction uses the is Equivalent direct Sum of is Hilbert Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/DirectSum.lean#L113-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations/DirectSum.lean#L113-L117

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

theorem GroundTheory.Automorphic.UnitaryRep.isEquivalent_directSum_of_isHilbertSum {π : UnitaryRep G H} {V : ι → Submodule ℂ H}
    [∀ i, CompleteSpace (V i)] (hinv : ∀ i, π.IsInvariant (V i))
    (hV : IsHilbertSum ℂ (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    π.IsEquivalent (directSum fun i => π.restrict (V i) (hinv i)) := by sorry
