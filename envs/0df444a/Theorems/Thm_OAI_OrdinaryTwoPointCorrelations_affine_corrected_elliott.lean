-- Prove2me | Theorems.Thm_OAI_OrdinaryTwoPointCorrelations_affine_corrected_elliott
-- name    : OAI.OrdinaryTwoPointCorrelations.affine_corrected_elliott
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-07T04:32:59.047828+00:00
-- url     : https://prove2.me/theorems/53422661-3f53-4f76-8e54-b0060a19d30a
-- statement:
--   The theorem states that, for any two functions f₁, f₂ : ℕ → ℂ that are multiplicative (f(mn)=f(m)f(n) whenever m,n are positive and coprime) and bounded by 1 in modulus on positive integers, if at least one of them is uniformly nonpretentious, then the affine correlation averages tend to zero. Uniform nonpretentiousness of f means that for every modulus q>0, every Dirichlet character χ mod q, and every real K, for all sufficiently large N and all real t with |t|≤N, the squared distance from f to the twist n ↦ χ(n)·exp(i t log n) is at least K, where the squared distance up to N is the sum over primes p≤N of (1 − Re(f(p)·conj(g(p))))/p. The conclusion holds for all natural numbers a₁, a₂, b₁, b₂ with a₁>0, a₂>0 and a₁b₂ ≠ a₂b₁: the sum over n=1,…,N of f₁(a₁n+b₁)·f₂(a₂n+b₂), divided by N, converges to 0 as N → ∞. The statement is admitted in the source without a proof.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/OrdinaryTwoPointCorrelations.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/OrdinaryTwoPointCorrelations.lean; bytes 2146..2592
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

theorem affine_corrected_elliott :
    ∀ f₁ f₂ : ℕ → ℂ, Multiplicative f₁ → Multiplicative f₂ →
      OneBounded f₁ → OneBounded f₂ →
      (UniformlyNonpretentious f₁ ∨ UniformlyNonpretentious f₂) →
      ∀ a₁ a₂ b₁ b₂ : ℕ, 0 < a₁ → 0 < a₂ → a₁ * b₂ ≠ a₂ * b₁ →
        Tendsto (fun N : ℕ => affineSum f₁ f₂ a₁ a₂ b₁ b₂ N / (N : ℂ)) atTop (nhds 0) := by
  sorry

end OrdinaryTwoPointCorrelations
end
end OAI
