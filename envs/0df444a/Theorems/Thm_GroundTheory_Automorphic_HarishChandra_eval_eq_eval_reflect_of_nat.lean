-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_eval_eq_eval_reflect_of_nat
-- name    : GroundTheory.Automorphic.HarishChandra.eval_eq_eval_reflect_of_nat
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:03:00.7552+00:00
-- url     : https://prove2.me/theorems/885ce237-4376-5285-a58f-b5b844400cf3
-- title:
--   Harish Chandra: eval eq eval reflect of nat
-- statement:
--   The Harish Chandra construction uses the eval eq eval reflect of nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L362-L400
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L362-L400

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

theorem GroundTheory.Automorphic.HarishChandra.eval_eq_eval_reflect_of_nat (hij : (j : ℕ) = i + 1) {z : U n}
    (hz : z ∈ Subalgebra.center ℂ (U n)) (lam : Fin n → ℂ) (m : ℕ) (hm : lam i - lam j = m) :
    eval lam (hcProjLin z) =
      eval (lam + fun k => ((m : ℂ) + 1) * rootAt (j, i) k) (hcProjLin z) := by sorry
