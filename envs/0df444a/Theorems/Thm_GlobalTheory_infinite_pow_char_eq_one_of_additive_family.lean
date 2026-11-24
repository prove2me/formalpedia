-- Prove2me | Theorems.Thm_GlobalTheory_infinite_pow_char_eq_one_of_additive_family
-- name    : GlobalTheory.infinite_pow_char_eq_one_of_additive_family
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:55:04.63988+00:00
-- url     : https://prove2.me/theorems/0c7d172f-f007-42b1-82d6-457c93c3cc63
-- title:
--   Global Theory: infinite pow char eq one of additive family
-- statement:
--   The Global Theory construction uses the infinite pow char eq one of additive family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/InfinitePowCharEqOneOfAdditiveFamily.lean#L14-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/InfinitePowCharEqOneOfAdditiveFamily.lean#L14-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_InfinitePowCharEqOneOfAdditiveFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.infinite_pow_char_eq_one_of_additive_family :
    ∀ (k : Type) [Field k] [Infinite k] (p : ℕ) [CharP k p] (M : Type) [Group M] (A : Type)
      [CommRing A] [Algebra k A] (r : ℕ) (f : Fin r → A) (ε : A →ₐ[k] k)
      (em : (A →ₐ[k] k) → M) (Pd : Polynomial k) (P : Fin r → Polynomial k)
      (ψ : k → (A →ₐ[k] k)), Algebra.adjoin k (Set.range f) = ⊤ → (∀ i, ε (f i) = 0) →
      Function.Injective em → em ε = 1 → Pd ≠ 0 → (∃ i, P i ≠ 0) →
      (∀ t, Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) →
      (∀ t t', Pd.eval t ≠ 0 → Pd.eval t' ≠ 0 → Pd.eval (t + t') ≠ 0 →
        em (ψ t) * em (ψ t') = em (ψ (t + t'))) → Infinite {x : M // x ^ p = 1} := by sorry
