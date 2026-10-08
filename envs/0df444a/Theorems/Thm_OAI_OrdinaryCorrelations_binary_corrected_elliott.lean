-- Prove2me | Theorems.Thm_OAI_OrdinaryCorrelations_binary_corrected_elliott
-- name    : OAI.OrdinaryCorrelations.binary_corrected_elliott
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-07T04:32:58.86387+00:00
-- url     : https://prove2.me/theorems/8dcdd820-9462-4b4b-9274-0f327f66a635
-- statement:
--   The theorem states that, for any two complex-valued arithmetic functions f₁, f₂ on the natural numbers, each bounded by 1 in absolute value (|fᵢ(n)| ≤ 1 for all n) and each multiplicative (fᵢ(mn)=fᵢ(m)fᵢ(n) for positive coprime m, n), if at least one of f₁, f₂ is uniformly nonpretentious, and h₁ ≠ h₂ are natural-number shifts, then the shifted correlation average (1/N)·Σ_{n=1}^{N} f₁(n+h₁)·f₂(n+h₂) tends to 0 as N → ∞. Here f is uniformly nonpretentious if, for every positive modulus q and every Dirichlet character χ mod q, the infimum over t in [−N, N] of the distance D(f,χ,t;N) tends to infinity as N → ∞. That distance is the square root of the sum over primes p ≤ N of (1 − Re(f(p)·conj(χ(p)·p^{it})))/p.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/OrdinaryElliott.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/OrdinaryElliott.lean; bytes 1124..1498
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_OrdinaryElliott

namespace OAI

noncomputable section

open scoped BigOperators

open Filter

namespace OrdinaryCorrelations

theorem binary_corrected_elliott
    (f₁ f₂ : ℕ → ℂ) (hf₁ : OneBounded f₁) (hf₂ : OneBounded f₂)
    (hm₁ : Multiplicative f₁) (hm₂ : Multiplicative f₂)
    (hNP : UniformlyNonpretentious f₁ ∨ UniformlyNonpretentious f₂)
    (h₁ h₂ : ℕ) (hne : h₁ ≠ h₂) :
    Tendsto (shiftAverage f₁ f₂ h₁ h₂) atTop (nhds 0) := by
  sorry

end OrdinaryCorrelations
end
end OAI
