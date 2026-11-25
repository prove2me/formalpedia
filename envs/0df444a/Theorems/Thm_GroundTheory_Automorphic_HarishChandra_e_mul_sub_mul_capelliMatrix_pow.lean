-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_e_mul_sub_mul_capelliMatrix_pow
-- name    : GroundTheory.Automorphic.HarishChandra.e_mul_sub_mul_capelliMatrix_pow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:30:00.492736+00:00
-- url     : https://prove2.me/theorems/c8a88d4b-de1b-4563-8c72-51543ed8be33
-- title:
--   Harish Chandra: e mul sub mul capelli Matrix pow
-- statement:
--   The Harish Chandra construction uses the e mul sub mul capelli Matrix pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Capelli.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Capelli.lean#L13-L17

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EMulSubMulCapelliMatrixPow
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Theorems.Thm_UpperTheory_Reformulated_B_Qk36_e_mul_sub_mul_capelliMatrix_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
variable {n : ℕ}

theorem GroundTheory.Automorphic.HarishChandra.e_mul_sub_mul_capelliMatrix_pow (a b : Fin n) (k : ℕ) (c d : Fin n) :
    e (a, b) * (capelliMatrix ^ k) c d - (capelliMatrix ^ k) c d * e (a, b) =
      (if b = c then (capelliMatrix ^ k) a d else 0) -
        (if d = a then (capelliMatrix ^ k) c b else 0) := by sorry
