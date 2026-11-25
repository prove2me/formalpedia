-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsInvariant_iSup
-- name    : GroundTheory.Automorphic.UnitaryRep.IsInvariant.iSup
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:26:19.629636+00:00
-- url     : https://prove2.me/theorems/9170d52d-52cb-4fd5-ab2d-e0a109645033
-- title:
--   Is Invariant: i Sup
-- statement:
--   The Is Invariant construction uses the i Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryRepresentations.lean#L21-L26

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_ExistsEqAlgebraMapOfIsSelfAdjoint
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_DirectSum
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_Integrated
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
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

theorem GroundTheory.Automorphic.UnitaryRep.IsInvariant.iSup {ι : Sort*} {V : ι → Submodule ℂ H} (h : ∀ i, π.IsInvariant (V i)) :
    π.IsInvariant (⨆ i, V i) := by sorry
