-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_eq_of_eval_eq_of_sub_nat
-- name    : GroundTheory.Automorphic.HarishChandra.eq_of_eval_eq_of_sub_nat
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:04:13.207681+00:00
-- url     : https://prove2.me/theorems/25a28a76-132b-4d28-babf-faa32022e221
-- title:
--   Harish Chandra: eq of eval eq of sub nat
-- statement:
--   The Harish Chandra construction uses the eq of eval eq of sub nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L412-L445
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L412-L445

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

theorem GroundTheory.Automorphic.HarishChandra.eq_of_eval_eq_of_sub_nat (hij : i ≠ j) {P Q : MvPolynomial (Fin n) ℂ}
    (h : ∀ lam : Fin n → ℂ, ∀ m : ℕ, lam i - lam j = m → eval lam P = eval lam Q) : P = Q := by sorry
