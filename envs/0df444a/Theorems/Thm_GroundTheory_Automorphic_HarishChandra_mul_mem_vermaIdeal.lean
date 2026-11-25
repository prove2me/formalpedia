-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mul_mem_vermaIdeal
-- name    : GroundTheory.Automorphic.HarishChandra.mul_mem_vermaIdeal
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:32:27.558191+00:00
-- url     : https://prove2.me/theorems/45a31189-7b8d-545c-8d44-a108c60605da
-- title:
--   Harish Chandra: mul mem verma Ideal
-- statement:
--   The Harish Chandra construction uses the mul mem verma Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L22-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L22-L35

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

theorem GroundTheory.Automorphic.HarishChandra.mul_mem_vermaIdeal (lam : Fin n → ℂ) (v : U n) {x : U n} (hx : x ∈ vermaIdeal lam) :
    v * x ∈ vermaIdeal lam := by sorry
