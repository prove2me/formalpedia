-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_pow_mul_h_sub_mem_vermaIdeal
-- name    : GroundTheory.Automorphic.HarishChandra.pow_mul_h_sub_mem_vermaIdeal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:03:22.286644+00:00
-- url     : https://prove2.me/theorems/7f05337b-93e4-597d-aab2-a33114df9460
-- title:
--   Harish Chandra: pow mul h sub mem verma Ideal
-- statement:
--   The Harish Chandra construction uses the pow mul h sub mem verma Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L326-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L326-L335

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

theorem GroundTheory.Automorphic.HarishChandra.pow_mul_h_sub_mem_vermaIdeal (lam : Fin n → ℂ) (m : ℕ) (hm : lam i - lam j = m) :
    e (j, i) ^ m * (e (i, i) - e (j, j)) - (m : ℂ) • e (j, i) ^ m ∈ vermaIdeal lam := by sorry
