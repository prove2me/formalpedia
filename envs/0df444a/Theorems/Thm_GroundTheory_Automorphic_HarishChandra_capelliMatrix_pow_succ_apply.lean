-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_capelliMatrix_pow_succ_apply
-- name    : GroundTheory.Automorphic.HarishChandra.capelliMatrix_pow_succ_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:30:11.531387+00:00
-- url     : https://prove2.me/theorems/f530e6d5-b1c7-4589-a6d7-5822912c4c09
-- title:
--   Harish Chandra: capelli Matrix pow succ apply
-- statement:
--   The Harish Chandra construction uses the capelli Matrix pow succ apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Capelli.lean#L28-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Capelli.lean#L28-L43

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EMulSubMulCapelliMatrixPow
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
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

theorem GroundTheory.Automorphic.HarishChandra.capelliMatrix_pow_succ_apply (m : ℕ) (c d : Fin n) :
    (capelliMatrix ^ (m + 1)) c d = ∑ i : Fin m → Fin n,
      word (List.ofFn fun t : Fin (m + 1) => ((Fin.cons c i : Fin (m + 1) → Fin n) t,
        (Fin.snoc i d : Fin (m + 1) → Fin n) t)) := by sorry
