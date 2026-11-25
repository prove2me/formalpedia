-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rep_apply_of_highestWeight
-- name    : GroundTheory.Automorphic.HarishChandra.rep_apply_of_highestWeight
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:24:34.573801+00:00
-- url     : https://prove2.me/theorems/dcd88a0d-078f-4b53-b81e-503e408829c6
-- title:
--   Harish Chandra: rep apply of highest Weight
-- statement:
--   The Harish Chandra construction uses the rep apply of highest Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Projection.lean#L266-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Projection.lean#L266-L291

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

theorem GroundTheory.Automorphic.HarishChandra.rep_apply_of_highestWeight {V : Type*} [AddCommGroup V] [Module ℂ V]
    (φ : U n →ₐ[ℂ] Module.End ℂ V) {v : V} (lam : Fin n → ℂ)
    (hup : ∀ a, IsUpper a → φ (e a) v = 0) (hH : ∀ k, φ (e (k, k)) v = lam k • v)
    {z : U n} (hz : ∀ k, e (k, k) * z = z * e (k, k)) :
    φ z v = eval lam (hcProjLin z) • v := by sorry
