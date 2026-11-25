-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcEmb_mul_e_pow
-- name    : GroundTheory.Automorphic.HarishChandra.hcEmb_mul_e_pow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:02:40.028055+00:00
-- url     : https://prove2.me/theorems/25e1de1c-d428-5556-8196-5316a7ebe5c5
-- title:
--   Harish Chandra: hc Emb mul e pow
-- statement:
--   The Harish Chandra construction uses the hc Emb mul e pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L206-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L206-L226

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

theorem GroundTheory.Automorphic.HarishChandra.hcEmb_mul_e_pow (a : Fin n × Fin n) (p : ℕ) (q : MvPolynomial (Fin n) ℂ) :
    hcEmb q * e a ^ p = e a ^ p * hcEmb (translate (fun k => (p : ℂ) * rootAt a k) q) := by sorry
