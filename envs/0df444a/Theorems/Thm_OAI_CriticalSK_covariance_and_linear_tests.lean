-- Prove2me | Theorems.Thm_OAI_CriticalSK_covariance_and_linear_tests
-- name    : OAI.CriticalSK.covariance_and_linear_tests
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:30.33556+00:00
-- url     : https://prove2.me/theorems/e9f896ea-430d-4539-82ad-5c5724d6096e
-- statement:
--   The theorem states that, for any positive real sequence M(n) tending to infinity, the following holds with probability tending to one as n grows. In the zero-field Sherrington-Kirkpatrick model on n spins σ ∈ {±1}^n, the couplings W_ij for pairs i<j are independent Gaussian variables with mean 0 and variance 1/n, and the Gibbs measure is proportional to exp(Σ_{i<j} W_ij σ_i σ_j). Let covarianceNorm(W) be the operator norm of the n×n covariance matrix of the spins under this Gibbs measure. Let linearRayleigh(W) be the supremum, over nonzero coefficient vectors a, of Var(Σ_i a_i σ_i) divided by the rate-one Dirichlet form of that linear observable, where the Dirichlet form is the sum over sites i of the Gibbs expectation of the squared difference between the observable and its average after a heat-bath resampling of site i. The claim is that the disorder probability of the event that both covarianceNorm(W) and linearRayleigh(W) lie in the interval [n^(2/3)/M(n), M(n)·n^(2/3)] tends to 1 as n → ∞.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CriticalSK.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CriticalSK.lean; bytes 4950..5569
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_CriticalSK

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory Filter

namespace CriticalSK

/-- Both the covariance operator norm and the linear inverse-Rayleigh supremum lie
between `n^(2/3) / M n` and `M n * n^(2/3)` with probability tending to one. -/
theorem covariance_and_linear_tests (M : ℕ → ℝ)
    (hMpos : ∀ n, 0 < M n) (hM : Tendsto M atTop atTop) :
    Tendsto (fun n : ℕ => (disorderLaw n {W |
      (n : ℝ) ^ ((2 : ℝ) / 3) / M n ≤ covarianceNorm W ∧
      covarianceNorm W ≤ M n * (n : ℝ) ^ ((2 : ℝ) / 3) ∧
      (n : ℝ) ^ ((2 : ℝ) / 3) / M n ≤ linearRayleigh W ∧
      linearRayleigh W ≤ M n * (n : ℝ) ^ ((2 : ℝ) / 3)}).toReal) atTop (𝓝 1) := by
  sorry

end CriticalSK
end
end OAI
