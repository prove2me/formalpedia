-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rep_center_apply_of_highestWeight
-- name    : GroundTheory.Automorphic.HarishChandra.rep_center_apply_of_highestWeight
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:47:27.886178+00:00
-- url     : https://prove2.me/theorems/f15aa417-fc00-422d-85db-ff98cad44912
-- title:
--   Harish Chandra: rep center apply of highest Weight
-- statement:
--   The Harish Chandra construction uses the rep center apply of highest Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Consequences.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Consequences.lean#L17-L24

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Consequences
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

theorem GroundTheory.Automorphic.HarishChandra.rep_center_apply_of_highestWeight {V : Type*} [AddCommGroup V] [Module ℂ V]
    (φ : U n →ₐ[ℂ] Module.End ℂ V) {v : V} (lam : Fin n → ℂ)
    (hup : ∀ a, IsUpper a → φ (e a) v = 0) (hH : ∀ k, φ (e (k, k)) v = lam k • v)
    (z : Subalgebra.center ℂ (U n)) :
    φ z v = eval (lam + rhoVec n) (harishChandraHom z) • v := by sorry
