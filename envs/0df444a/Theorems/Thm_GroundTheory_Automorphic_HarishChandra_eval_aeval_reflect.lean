-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_eval_aeval_reflect
-- name    : GroundTheory.Automorphic.HarishChandra.eval_aeval_reflect
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:03:39.016943+00:00
-- url     : https://prove2.me/theorems/a9a61ff0-96bd-45f6-bb02-2cafce770e12
-- title:
--   Harish Chandra: eval aeval reflect
-- statement:
--   The Harish Chandra construction uses the eval aeval reflect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L402-L410
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L402-L410

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

theorem GroundTheory.Automorphic.HarishChandra.eval_aeval_reflect (r : Fin n → ℂ) (q : MvPolynomial (Fin n) ℂ) (mu : Fin n → ℂ) :
    eval mu (aeval (fun k => X k + (X i - X j + 1) * C (r k)) q) =
      eval (mu + fun k => (mu i - mu j + 1) * r k) q := by sorry
