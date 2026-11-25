-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_const_of_forall_rotate
-- name    : GroundTheory.Automorphic.HarishChandra.const_of_forall_rotate
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:02:34.834217+00:00
-- url     : https://prove2.me/theorems/96f4a79a-e35f-5bf6-b2e0-075b9f2180d2
-- title:
--   Harish Chandra: const of forall rotate
-- statement:
--   The Harish Chandra construction uses the const of forall rotate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L109-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L109-L116

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_LeadingTerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}

theorem GroundTheory.Automorphic.HarishChandra.const_of_forall_rotate {k : ℕ} {i : Fin (k + 1) → Fin n}
    (h : ∀ t, i t = i (finRotate (k + 1) t)) (t : Fin (k + 1)) : i t = i 0 := by sorry
