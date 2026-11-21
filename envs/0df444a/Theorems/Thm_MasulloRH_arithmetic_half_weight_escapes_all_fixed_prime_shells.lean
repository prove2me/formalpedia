-- Prove2me | Theorems.Thm_MasulloRH_arithmetic_half_weight_escapes_all_fixed_prime_shells
-- name    : MasulloRH.arithmetic_half_weight_escapes_all_fixed_prime_shells
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T05:23:17.42451+00:00
-- url     : https://prove2.me/theorems/98b3ba39-391f-499f-81a0-d10f32244ea5
-- title:
--   The half-weight prime signal escapes every fixed finite set of local prime shells
-- statement:
--   There is one smooth real test supported in $(1,32)$ with both $M(1)=M(-1/2)=0$ and one $c>0$ such that, after removing all prime powers at any fixed finite collection of primes from its translated half-weight von Mangoldt sum, the remainder is at least $c\sqrt X$ for every sufficiently large $X$. The bound also holds when an arbitrary finite subset of exponents is selected at each omitted prime. The total absolute local contribution at the fixed primes is bounded over every dilation and choice of exponents. Thus each fixed prime coordinate tends to zero after normalization by $\sqrt X$, while the full signed mass stays positive.
-- source:
--   Masullo, (11.3.2.1–5), (12.5.1.1). Builds on Yi’s verified two-moment discriminator and the earlier translated arithmetic half-weight theorem f2d1cdcf-dc61-4c31-ba7e-e336d378ddb3 using Yuxuan Xu’s Chebyshev PNT.

import Mathlib
open Filter MeasureTheory Set
open scoped Topology ArithmeticFunction

theorem MasulloRH.arithmetic_half_weight_escapes_all_fixed_prime_shells :
    ∃ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ Set.Ioo 1 32 ∧
      HasMellin (fun t => (f t : ℂ)) 1 0 ∧ HasMellin (fun t => (f t : ℂ)) (-(1/2) : ℂ) 0 ∧
      ∃ c : ℝ, 0 < c ∧ ∀ P : Finset ℕ, (∀ p ∈ P, 2 ≤ p) →
        (∃ D : ℝ, ∀ (X : ℝ) (J : ℕ → Finset ℕ),
          (∑ p ∈ P, ∑ k ∈ J p, |Real.log (p:ℝ) * (Real.sqrt p)⁻¹ ^ k * f ((p:ℝ)^k/X)|) ≤ D) ∧
        ∀ᶠ X : ℝ in atTop, ∀ J : ℕ → Finset ℕ,
          c * Real.sqrt X ≤
            (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊32*X⌋₊, ArithmeticFunction.vonMangoldt n / Real.sqrt n * f ((n:ℝ)/X)) -
            ∑ p ∈ P, ∑ k ∈ J p, Real.log (p:ℝ) * (Real.sqrt p)⁻¹ ^ k * f ((p:ℝ)^k/X) := by sorry
