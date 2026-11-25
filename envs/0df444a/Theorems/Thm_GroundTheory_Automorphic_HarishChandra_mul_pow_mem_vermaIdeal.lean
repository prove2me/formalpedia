-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mul_pow_mem_vermaIdeal
-- name    : GroundTheory.Automorphic.HarishChandra.mul_pow_mem_vermaIdeal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:05:40.582961+00:00
-- url     : https://prove2.me/theorems/2fbb88c4-e40c-4c12-b30c-b63f54181400
-- title:
--   Harish Chandra: mul pow mem verma Ideal
-- statement:
--   The Harish Chandra construction uses the mul pow mem verma Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L337-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L337-L360

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
variable {i j : Fin n}

theorem GroundTheory.Automorphic.HarishChandra.mul_pow_mem_vermaIdeal (hij : (j : ℕ) = i + 1) (lam : Fin n → ℂ) (m : ℕ)
    (hm : lam i - lam j = m) {x : U n} (hx : x ∈ nPlusU n) :
    x * e (j, i) ^ (m + 1) ∈ vermaIdeal lam := by sorry
