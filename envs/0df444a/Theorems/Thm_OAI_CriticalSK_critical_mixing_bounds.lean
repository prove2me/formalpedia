-- Prove2me | Theorems.Thm_OAI_CriticalSK_critical_mixing_bounds
-- name    : OAI.CriticalSK.critical_mixing_bounds
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:30.468365+00:00
-- url     : https://prove2.me/theorems/82bab5df-c2fb-4aa7-82d3-51851e759cbc
-- statement:
--   The theorem states that for every ε>0 the following two limits equal 1, for the Sherrington–Kirkpatrick-type spin system defined in the context file. For n spins x∈{±1}ⁿ, the disorder W assigns a real coupling to each pair i<j, drawn independently from a centered Gaussian with variance 1/n (the law disorderLaw n). The energy is H(x)=Σ_{i<j} W_{ij}xᵢxⱼ, with no extra inverse-temperature parameter, and the Gibbs distribution is exp(H(x)) divided by the sum of exp(H) over all configurations. The site kernel for coordinate i resamples spin i from the Gibbs distribution conditioned on the other spins. The discrete kernel averages these n site kernels with weight 1/n each, the generator is the sum over i of (site kernel i minus identity), and the continuous-time kernel at time t is the matrix exponential exp(tL) of the generator. Distance is total variation (half the ℓ¹ distance) to the Gibbs distribution. The continuous mixing time is the infimum of t≥0 such that the distance from every starting configuration is at most 1/4, and the discrete mixing time is the least natural number k with this property for the kernel's kth power. The first limit says that the probability, under the disorder law, that n^{2/3−ε} ≤ continuous mixing time ≤ e^{εn} tends to 1 as n→∞. The second says that the probability that n^{5/3−ε} ≤ discrete mixing time ≤ e^{εn} also tends to 1. The result is stated in the source with its proof omitted (sorry).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CriticalSKMixing.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CriticalSKMixing.lean; bytes 2256..2732
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_CriticalSKMixing

namespace OAI

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace CriticalSK

theorem critical_mixing_bounds (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (disorderLaw n {W |
      (n : ℝ) ^ ((2 : ℝ) / 3 - ε) ≤ continuousMixingTime W ∧
      continuousMixingTime W ≤ Real.exp (ε * n)}).toReal) atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ => (disorderLaw n {W |
      (n : ℝ) ^ ((5 : ℝ) / 3 - ε) ≤ (discreteMixingTime W : ℝ) ∧
      (discreteMixingTime W : ℝ) ≤ Real.exp (ε * n)}).toReal) atTop (𝓝 1) := by
  sorry

end CriticalSK
end
end OAI
