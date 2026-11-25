-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_vermaCoord_mul_e_sub
-- name    : GroundTheory.Automorphic.HarishChandra.vermaCoord_mul_e_sub
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:03:37.619587+00:00
-- url     : https://prove2.me/theorems/447df6f4-e852-4a29-9be1-c06e94587a38
-- title:
--   Harish Chandra: verma Coord mul e sub
-- statement:
--   The Harish Chandra construction uses the verma Coord mul e sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L134-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L134-L142

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

theorem GroundTheory.Automorphic.HarishChandra.vermaCoord_mul_e_sub (lam : Fin n → ℂ) (u : U n) (k : Fin n) :
    vermaCoord lam (u * (e (k, k) - algebraMap ℂ (U n) (lam k))) = 0 := by sorry
