-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_eval_eq_eval_reflect
-- name    : GroundTheory.Automorphic.HarishChandra.eval_eq_eval_reflect
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:03:57.59077+00:00
-- url     : https://prove2.me/theorems/f4bee5a3-ab8f-41bb-9d4f-93ecff74173d
-- title:
--   Harish Chandra: eval eq eval reflect
-- statement:
--   The Harish Chandra construction uses the eval eq eval reflect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L447-L458
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L447-L458

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

theorem GroundTheory.Automorphic.HarishChandra.eval_eq_eval_reflect (hij : (j : ℕ) = i + 1) {z : U n}
    (hz : z ∈ Subalgebra.center ℂ (U n)) (lam : Fin n → ℂ) :
    eval lam (hcProjLin z) =
      eval (lam + fun k => (lam i - lam j + 1) * rootAt (j, i) k) (hcProjLin z) := by sorry
