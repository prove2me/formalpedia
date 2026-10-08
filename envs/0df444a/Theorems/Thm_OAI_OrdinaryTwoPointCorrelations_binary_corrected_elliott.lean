-- Prove2me | Theorems.Thm_OAI_OrdinaryTwoPointCorrelations_binary_corrected_elliott
-- name    : OAI.OrdinaryTwoPointCorrelations.binary_corrected_elliott
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-07T04:32:59.178562+00:00
-- url     : https://prove2.me/theorems/69a377e8-35c7-4077-96b9-ffbe938b7a5e
-- statement:
--   The theorem states that, for any two functions f₁, f₂ from the natural numbers to the complex numbers that are multiplicative (f(mn)=f(m)f(n) for all positive coprime m and n) and one-bounded (|f(n)|≤1 for every positive n), if at least one of them is uniformly nonpretentious, then for any two distinct natural numbers h₁ ≠ h₂ the normalized correlation sum (1/N)·Σ_{n=1}^{N} f₁(n+h₁)·f₂(n+h₂) tends to 0 as N → ∞. Here f is uniformly nonpretentious if, for every modulus q>0, every Dirichlet character χ mod q, and every real K, for all sufficiently large N and every real t with |t|≤N, the squared distance between f and the twist n ↦ χ(n)·n^{it} up to N is at least K. That squared distance is the sum over primes p≤N of (1 − Re(f(p)·conj(g(p))))/p, with g the twist. In effect this distance tends to infinity uniformly over all such t and every character. The hypotheses do not require h₁ and h₂ to be positive.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/OrdinaryTwoPointCorrelations.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/OrdinaryTwoPointCorrelations.lean; bytes 1753..2144
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_OrdinaryTwoPointCorrelations

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate

open Filter

namespace OrdinaryTwoPointCorrelations

open TwoPointCorrelations

theorem binary_corrected_elliott :
    ∀ f₁ f₂ : ℕ → ℂ, Multiplicative f₁ → Multiplicative f₂ →
      OneBounded f₁ → OneBounded f₂ →
      (UniformlyNonpretentious f₁ ∨ UniformlyNonpretentious f₂) →
      ∀ h₁ h₂ : ℕ, h₁ ≠ h₂ →
        Tendsto (fun N : ℕ => correlationSum f₁ f₂ h₁ h₂ N / (N : ℂ)) atTop (nhds 0) := by
  sorry

end OrdinaryTwoPointCorrelations
end
end OAI
