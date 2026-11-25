-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_lift_indicator
-- name    : GroundTheory.Automorphic.Whittaker.exists_lift_indicator
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:34:43.500883+00:00
-- url     : https://prove2.me/theorems/fb1fd4dc-145b-4a98-bbb2-5dedef524aeb
-- title:
--   Whittaker: exists lift indicator
-- statement:
--   The Whittaker construction uses the exists lift indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L157-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L157-L170

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

theorem GroundTheory.Automorphic.Whittaker.exists_lift_indicator {U O A : Set X} (hU : IsOpen U) (hOU : O ⊆ U) (hAO : A ⊆ O)
    (hAc : IsCompact A) (hAo : IsOpen ((Subtype.val : O → X) ⁻¹' A)) :
    ∃ f ∈ supportedIn U, ∀ x ∈ O, f x = A.indicator 1 x := by sorry
