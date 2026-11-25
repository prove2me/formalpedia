-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_center_of_commute_e
-- name    : GroundTheory.Automorphic.HarishChandra.mem_center_of_commute_e
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:30:01.54155+00:00
-- url     : https://prove2.me/theorems/249c8459-e903-4476-a9be-9291b383b211
-- title:
--   Harish Chandra: mem center of commute e
-- statement:
--   The Harish Chandra construction uses the mem center of commute e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemCenterOfCommuteE.lean#L78-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemCenterOfCommuteE.lean#L78-L88

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
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
variable {n : ℕ}

theorem GroundTheory.Automorphic.HarishChandra.mem_center_of_commute_e {z : U n} (hz : ∀ a, e a * z = z * e a) :
    z ∈ Subalgebra.center ℂ (U n) := by sorry
