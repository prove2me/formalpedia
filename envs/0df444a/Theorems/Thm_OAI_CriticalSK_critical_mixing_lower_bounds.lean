-- Prove2me | Theorems.Thm_OAI_CriticalSK_critical_mixing_lower_bounds
-- name    : OAI.CriticalSK.critical_mixing_lower_bounds
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:30.581984+00:00
-- url     : https://prove2.me/theorems/62eb0a28-364c-426f-8274-990f3f5857e9
-- statement:
--   The theorem states that, for every real ε>0, two probability statements hold in the zero-field Sherrington–Kirkpatrick-type model on n spins with disorder W, where W assigns an independent centered Gaussian coupling of variance 1/n to each pair of sites i<j. The Gibbs measure on spin configurations in {±1}^n is proportional to exp of the sum over pairs of W_ij σ_i σ_j. Heat bath dynamics resample one site from its conditional Gibbs law given the other sites. In the continuous-time chain each site is updated at rate one, so the kernel at time t is the matrix exponential of t times the generator, the sum over sites of (site kernel minus identity). In the discrete chain each attempt chooses a site uniformly and applies its heat bath kernel. The mixing time of either chain is the smallest time (respectively number of attempts) after which the total variation distance to the Gibbs measure is at most 1/4 from every initial configuration, that is, the worst start. The first claim is that the disorder probability that the continuous mixing time is at least n^(2/3−ε) tends to 1 as n→∞. The second is that the disorder probability that the discrete mixing time is at least n^(5/3−ε) tends to 1 as n→∞. The proof is admitted in the source, not established here.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CriticalSK.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CriticalSK.lean; bytes 5571..6043
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_CriticalSK

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory Filter

namespace CriticalSK

/-- Worst-start mixing takes at least `n^(2/3-ε)` continuous time and
`n^(5/3-ε)` discrete attempts with probability tending to one. -/
theorem critical_mixing_lower_bounds (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (disorderLaw n).real {W |
      (n : ℝ) ^ (2 / 3 - ε) ≤ continuousMixingTime W}) atTop (𝓝 1) ∧
    Tendsto (fun n => (disorderLaw n).real {W |
      (n : ℝ) ^ (5 / 3 - ε) ≤ (discreteMixingTime W : ℝ)}) atTop (𝓝 1) := by
  sorry

end CriticalSK
end
end OAI
