-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rep_center_apply_mem_span_of_conj
-- name    : GroundTheory.Automorphic.HarishChandra.rep_center_apply_mem_span_of_conj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:58:28.161112+00:00
-- url     : https://prove2.me/theorems/925479ee-6b64-58bb-9ceb-429bd3235c67
-- title:
--   Harish Chandra: rep center apply mem span of conj
-- statement:
--   The Harish Chandra construction uses the rep center apply mem span of conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Consequences.lean#L60-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Consequences.lean#L60-L68

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

theorem GroundTheory.Automorphic.HarishChandra.rep_center_apply_mem_span_of_conj {V : Type*} [AddCommGroup V] [Module ℂ V]
    (φ : U n →ₐ[ℂ] Module.End ℂ V) (g : (gl n)ˣ) {v : V} (lam : Fin n → ℂ)
    (hup : ∀ a, IsUpper a → φ (conjU g (e a)) v = 0)
    (hH : ∀ k, φ (conjU g (e (k, k))) v = lam k • v) {z : U n} (hz : z ∈ Subalgebra.center ℂ (U n)) :
    ∃ c : ℂ, φ z v = c • v := by sorry
