-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_isCompact_isOpen_between
-- name    : GroundTheory.Automorphic.Whittaker.exists_isCompact_isOpen_between
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:51.189648+00:00
-- url     : https://prove2.me/theorems/5395258e-9f77-422e-a2f9-8c6832c92d7b
-- title:
--   Whittaker: exists is Compact is Open between
-- statement:
--   The Whittaker construction uses the exists is Compact is Open between property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L80-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L80-L88

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

theorem GroundTheory.Automorphic.Whittaker.exists_isCompact_isOpen_between {A V : Set X} (hA : IsCompact A) (hV : IsOpen V)
    (hAV : A ⊆ V) : ∃ B : Set X, IsCompact B ∧ IsOpen B ∧ A ⊆ B ∧ B ⊆ V := by sorry
