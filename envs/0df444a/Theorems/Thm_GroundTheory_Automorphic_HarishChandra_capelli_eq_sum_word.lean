-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_capelli_eq_sum_word
-- name    : GroundTheory.Automorphic.HarishChandra.capelli_eq_sum_word
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:45.339565+00:00
-- url     : https://prove2.me/theorems/f070cb87-f487-4148-bb5d-664dcfe52b63
-- title:
--   Harish Chandra: capelli eq sum word
-- statement:
--   The Harish Chandra construction uses the capelli eq sum word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Capelli.lean#L45-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Capelli.lean#L45-L58

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

theorem GroundTheory.Automorphic.HarishChandra.capelli_eq_sum_word (k : ℕ) :
    capelli (n := n) (k + 1) = ∑ i : Fin (k + 1) → Fin n,
      word (List.ofFn fun t : Fin (k + 1) => (i t, i (finRotate (k + 1) t))) := by sorry
