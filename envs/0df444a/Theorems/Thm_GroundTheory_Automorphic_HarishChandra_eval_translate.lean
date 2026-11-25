-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_eval_translate
-- name    : GroundTheory.Automorphic.HarishChandra.eval_translate
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:17:49.388042+00:00
-- url     : https://prove2.me/theorems/8210f533-baf7-5e8d-a413-3d1d1ba34d84
-- title:
--   Harish Chandra: eval translate
-- statement:
--   The Harish Chandra construction uses the eval translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Projection.lean#L298-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Projection.lean#L298-L305

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

theorem GroundTheory.Automorphic.HarishChandra.eval_translate (c lam : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ) :
    eval lam (translate c p) = eval (lam + c) p := by sorry
