-- Prove2me | Theorems.Thm_OAI_SKValue_value_consequences
-- name    : OAI.SKValue.value_consequences
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:18.348477+00:00
-- url     : https://prove2.me/theorems/716b474d-eaef-43ef-a426-41f38acc1f63
-- statement:
--   The theorem states three consequences, for a Brownian space W (a probability space carrying a strongly measurable real Brownian motion B indexed by nonnegative reals) and an order parameter γ (a real function that on [0,1) is nonnegative, monotone and right-continuous, and is integrable on (0,1]). Here phi(t,x) is the supremum, over progressive controls α with |α|≤1 adapted to the Brownian increments after time t, of the expected value of |x + B₁ − B_t + ∫₀^{1−t} γ(t+s)α_s ds| − ½∫₀^{1−t} γ(t+s)α_s² ds; gradient and curvature are its first and second x-derivatives (Lean's deriv); parisi(γ) = phi(0,0) − ½∫₀¹ tγ(t)dt; and IsMinimizer means parisi(γ) ≤ parisi(η) for every order parameter η. IsDiffusion for a process X means that X, stopped at time 1, is adapted to the Brownian filtration, and that almost surely X is continuous on [0,1] and satisfies X_t = B_t + ∫₀ᵗ γ(s)·gradient(s, X_s) ds for all t in [0,1]. groundStateSequence(n) is (1/n) times the Gaussian expectation, over i.i.d. standard normal couplings J_{ij} with i<j, of the maximum over spin vectors σ∈{±1}ⁿ of n^{-1/2}Σ_{i<j} J_{ij}σ_iσ_j, and groundStateValue is its limit as n→∞ (taken with Lean's limUnder). First, for every minimizer γ and every diffusion X, ScalarValueConclusion holds: groundStateSequence converges to groundStateValue; and there is a random variable U such that the gradient process, frozen at U from time 1 on, is a martingale; almost surely |U|≤1, U²=1 and gradient(t,X_t) → U as t↑1; the mean-square distance E[(gradient(t,X_t) − U)²] tends to 0 as t↑1; groundStateValue equals E|X₁| − ∫₀¹ tγ(t)dt, equals E[U·B₁], and equals ∫₀¹ E[curvature(t,X_t)]dt, with that integrand interval integrable on [0,1]. Second, for the same hypotheses and any T with 0<T<1, FiniteGaussianConclusion holds: for all large N the normalizers of the Euler-scheme curvature coefficients at mesh steps j<N are positive; a shifted sum of products of Gaussian-projection coefficients, built from a rounded sign of gradient(T, Euler path) + 2Φ(z_N) − 1, converges as N→∞ to ∫₀ᵀ E[curvature(t,X_t)]dt; and ∫₀^S E[curvature(t,X_t)]dt tends to groundStateValue as S↑1. Third, for every W and every minimizer γ, groundStateValue = parisi(γ).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKValue.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SKValue.lean; bytes 7554..8074
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SKValue

namespace OAI

open MeasureTheory ProbabilityTheory Filter Set

open scoped Topology ENNReal NNReal BigOperators

namespace SKValue

attribute [instance] BrownianSpace.measurableSpace BrownianSpace.probability

theorem value_consequences :
    (∀ (W : BrownianSpace) (γ : OrderParameter) (X : ℝ → W.Ω → ℝ),
      IsMinimizer W γ → IsDiffusion W γ X → ScalarValueConclusion W γ X) ∧
    (∀ (W : BrownianSpace) (γ : OrderParameter) (X : ℝ → W.Ω → ℝ) (T : ℝ),
      0 < T → T < 1 → IsMinimizer W γ → IsDiffusion W γ X →
      FiniteGaussianConclusion W γ X T) ∧
    (∀ (W : BrownianSpace) (γ : OrderParameter),
      IsMinimizer W γ → groundStateValue = parisi W γ) := by
  sorry

end SKValue
end OAI
