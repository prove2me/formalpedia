-- Prove2me | Theorems.Thm_LogSupermodularBIS_Main_Supplement_lemma_A_6
-- name    : LogSupermodularBIS.Main.Supplement.lemma_A_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:34:22.903196+00:00
-- url     : https://prove2.me/theorems/4835f6eb-4ae2-4f65-81e2-0fe95fd9ba88
-- title:
--   Lemma A.6 — finite rational choices using exactly ℓ fair bits
-- statement:
--   Let $n\ge1$ and let $\omega_0,\ldots,\omega_{n-1}$ be positive rational weights whose reduced numerators and denominators have at most $L$ bits. For every integer $\ell\ge1$, one uniform finite bit program draws an index using exactly $\ell$ independent fair bits and at most $C(1+n+L+\ell)^a$ bit operations on every tape, where the absolute $C>0$ and natural degree $a$ are fixed before the inputs. Its law $\widehat p$ satisfies
--   $$
--   \left\|\widehat p-\left(\frac{\omega_j}{\sum_i\omega_i}\right)_{j=0}^{n-1}\right\|_{\rm TV}
--   \le(n-1)2^{-\ell}.
--   $$
--   The program always returns an index. It implements the source proof's dyadic inverse transform: read the $\ell$ bits as a uniform dyadic grid point and return the first cumulative normalized weight strictly above it. The singleton case has error zero. No denominator divisibility or power-of-two restriction is imposed on the weights.
--
--   This result supplies bounded fair-bit transitions and the finite enumeration branch of the bit implementation.
--
--   Differences from the source:
--   - encoding: ordered indices 1,…,nω → Fin n with indices 0,…,n−1; reason: renumbering preserves the weight order and normalized probabilities
--   - encoding: poly(nω,ℓω,ℓ) bit operations and ℓ fair bits → one finite binary-stack program, uniform absolute C>0 and degree a, cost C(1+n+L+ℓ)^a and exactly ℓ coin instructions on every tape; reason: unfolds polynomial notation in an operational bit model and implements the inverse-transform construction in the proof
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), pp. 41–42 (PDF 42–43), Lemma A.6

import Mathlib
import Definitions.Def_LogSupermodularBIS_Main_Supplement_FiniteChoice

set_option autoImplicit false

namespace LogSupermodularBIS.Main.Supplement

/-- Lemma A.6, pp.41–42 (PDF 42–43), including its bounded-bit construction. -/
theorem lemma_A_6 :
    ∃ P : BitProgram, ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ,
      ∀ (n L ℓ : ℕ) (ω : Fin n → ℚ), 1 ≤ n → 1 ≤ ℓ →
        (∀ i, 0 < ω i) → (∀ i, LogSupermodularBIS.Main.bitLength (ω i) ≤ L) →
        let input := choiceInput ω L ℓ
        let T := C * (1 + (n : ℝ) + L + ℓ) ^ a
        BitTerminates P none input T (fun bs => ∃ j : Fin n, bs = encNat j.val) ∧
        (∀ u : ℕ → Bool, (execution P none input T u).cursor = ℓ ∧
          bitOutput P none input T u = encNat (dyadicChoice ω ℓ u)) ∧
        finiteTV (fun j : Fin n => bitMass P none input T (encNat j.val)) (choiceLaw ω) ≤
          ((n : ℝ) - 1) * (2 : ℝ) ^ (-(ℓ : ℤ)) := by sorry

end LogSupermodularBIS.Main.Supplement
