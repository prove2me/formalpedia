-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_e_diag_mul_e_pow
-- name    : GroundTheory.Automorphic.HarishChandra.e_diag_mul_e_pow
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:53:56.019578+00:00
-- url     : https://prove2.me/theorems/f73c6427-adc2-53ca-bb66-0909a33e537a
-- title:
--   Harish Chandra: e diag mul e pow
-- statement:
--   The Harish Chandra construction uses the e diag mul e pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L190-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L190-L204

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

theorem GroundTheory.Automorphic.HarishChandra.e_diag_mul_e_pow (k : Fin n) (a : Fin n × Fin n) (p : ℕ) :
    e (k, k) * e a ^ p = e a ^ p * e (k, k) + ((p : ℂ) * rootAt a k) • e a ^ p := by sorry
