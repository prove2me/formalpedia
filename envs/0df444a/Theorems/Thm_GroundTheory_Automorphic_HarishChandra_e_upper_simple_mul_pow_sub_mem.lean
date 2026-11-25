-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_e_upper_simple_mul_pow_sub_mem
-- name    : GroundTheory.Automorphic.HarishChandra.e_upper_simple_mul_pow_sub_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:04:08.171024+00:00
-- url     : https://prove2.me/theorems/9dba62f6-fd4b-42cd-90d4-d184026b74fb
-- title:
--   Harish Chandra: e upper simple mul pow sub mem
-- statement:
--   The Harish Chandra construction uses the e upper simple mul pow sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L282-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L282-L318

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

theorem GroundTheory.Automorphic.HarishChandra.e_upper_simple_mul_pow_sub_mem (hij : (j : ℕ) = i + 1) (m : ℕ) :
    e (i, j) * e (j, i) ^ (m + 1) -
      (((m : ℂ) + 1) • (e (j, i) ^ m * (e (i, i) - e (j, j))) - (((m : ℂ) + 1) * m) • e (j, i) ^ m)
      ∈ nPlusU n := by sorry
