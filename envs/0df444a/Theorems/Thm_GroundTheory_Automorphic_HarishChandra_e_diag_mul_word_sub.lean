-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_e_diag_mul_word_sub
-- name    : GroundTheory.Automorphic.HarishChandra.e_diag_mul_word_sub
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:29:39.50867+00:00
-- url     : https://prove2.me/theorems/6f5c4e80-a94b-4422-9e64-f6475f118110
-- title:
--   Harish Chandra: e diag mul word sub
-- statement:
--   The Harish Chandra construction uses the e diag mul word sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L335-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L335-L347

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
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

theorem GroundTheory.Automorphic.HarishChandra.e_diag_mul_word_sub (k : Fin n) (w : List (Fin n × Fin n)) :
    e (k, k) * word w - word w * e (k, k) = (((w.map fun a => rootAt a k).sum : ℤ) : ℂ) • word w := by sorry
