-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_top_le_topologicalClosure_iSup
-- name    : GroundTheory.Automorphic.UnitaryRep.top_le_topologicalClosure_iSup
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:24:17.671334+00:00
-- url     : https://prove2.me/theorems/0bffeca6-8c9f-4dbd-9d86-450d77aca2d0
-- title:
--   Unitary Rep: top le topological Closure i Sup
-- statement:
--   The Unitary Rep construction uses the top le topological Closure i Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations.lean#L44-L50

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_ExistsEqAlgebraMapOfIsSelfAdjoint
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_DirectSum
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_Integrated
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsInvariant_topologicalClosure

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
open scoped InnerProductSpace
open ContinuousLinearMap Submodule
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable {π : UnitaryRep G H}
variable {J : Type*} {V : J → Submodule ℂ H} [∀ j, CompleteSpace (V j)]

theorem GroundTheory.Automorphic.UnitaryRep.top_le_topologicalClosure_iSup
    (hV : IsHilbertSum ℂ (fun j => V j) fun j => (V j).subtypeₗᵢ) :
    ⊤ ≤ (⨆ j, V j).topologicalClosure := by sorry
