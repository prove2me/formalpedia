-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcEmb_sub_eval_mem_vermaIdeal
-- name    : GroundTheory.Automorphic.HarishChandra.hcEmb_sub_eval_mem_vermaIdeal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:03:59.186847+00:00
-- url     : https://prove2.me/theorems/d06a0a96-e529-40bb-9c6e-ff62006ce7e5
-- title:
--   Harish Chandra: hc Emb sub eval mem verma Ideal
-- statement:
--   The Harish Chandra construction uses the hc Emb sub eval mem verma Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L37-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L37-L53

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

theorem GroundTheory.Automorphic.HarishChandra.hcEmb_sub_eval_mem_vermaIdeal (lam : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ) :
    hcEmb p - algebraMap ℂ (U n) (eval lam p) ∈ vermaIdeal lam := by sorry
