-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_eval_harishChandraHom
-- name    : GroundTheory.Automorphic.HarishChandra.eval_harishChandraHom
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:23:11.189941+00:00
-- url     : https://prove2.me/theorems/cda26917-9281-537f-b045-97c600757e6b
-- title:
--   Harish Chandra: eval harish Chandra Hom
-- statement:
--   The Harish Chandra construction uses the eval harish Chandra Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Projection.lean#L314-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Projection.lean#L314-L316

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
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

theorem GroundTheory.Automorphic.HarishChandra.eval_harishChandraHom (z : Subalgebra.center ℂ (U n)) (lam : Fin n → ℂ) :
    eval lam (harishChandraHom z) = eval (lam - rhoVec n) (hcProjLin (z : U n)) := by sorry
