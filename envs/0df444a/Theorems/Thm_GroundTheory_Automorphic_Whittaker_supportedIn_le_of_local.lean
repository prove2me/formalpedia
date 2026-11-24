-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_supportedIn_le_of_local
-- name    : GroundTheory.Automorphic.Whittaker.supportedIn_le_of_local
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:41.81579+00:00
-- url     : https://prove2.me/theorems/196a71c5-64b4-4a06-af4c-c5add2d7386e
-- title:
--   Whittaker: supported In le of local
-- statement:
--   The Whittaker construction uses the supported In le of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L260-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L260-L304

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology
variable {X : Type*} [TopologicalSpace X]
variable [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]

theorem GroundTheory.Automorphic.Whittaker.supportedIn_le_of_local {V : Set X} {M : Submodule ℂ (X → ℂ)}
    (hloc : ∀ x ∈ V, ∃ V' : Set X, IsOpen V' ∧ x ∈ V' ∧ supportedIn V' ≤ M) :
    supportedIn V ≤ M := by sorry
