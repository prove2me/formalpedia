-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mul_e_sub_mem_vermaIdeal
-- name    : GroundTheory.Automorphic.HarishChandra.mul_e_sub_mem_vermaIdeal
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:52:52.072864+00:00
-- url     : https://prove2.me/theorems/9d33d28e-467f-4262-b5d9-05090e1da713
-- title:
--   Harish Chandra: mul e sub mem verma Ideal
-- statement:
--   The Harish Chandra construction uses the mul e sub mem verma Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L18-L20

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_VermaCoordEqZeroOfMemNPlusU
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

theorem GroundTheory.Automorphic.HarishChandra.mul_e_sub_mem_vermaIdeal (lam : Fin n → ℂ) (u : U n) (k : Fin n) :
    u * (e (k, k) - algebraMap ℂ (U n) (lam k)) ∈ vermaIdeal lam := by sorry
