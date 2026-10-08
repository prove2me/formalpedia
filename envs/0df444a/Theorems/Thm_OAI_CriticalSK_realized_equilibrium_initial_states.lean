-- Prove2me | Theorems.Thm_OAI_CriticalSK_realized_equilibrium_initial_states
-- name    : OAI.CriticalSK.realized_equilibrium_initial_states
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:30.742638+00:00
-- url     : https://prove2.me/theorems/fe9a0d10-6168-4051-8789-2d89b91a8476
-- statement:
--   The theorem states a conjunction of two limit results for the zero-field Sherrington-Kirkpatrick-type model on n spins, with independent Gaussian edge couplings W_e of mean 0 and variance 1/n, one for each pair i<j, whose joint law is disorderLaw(n). For a coupling realization W, the Gibbs measure on spin configurations x in {±1}^n is proportional to exp of the sum over edges of W_{ij}x_i x_j. The continuous-time heat-bath dynamics updates each site at rate one, with kernel exp(t·generator), and the discrete one chooses a site uniformly at each attempt; distances to the Gibbs measure are measured in total variation (half the l1 distance). continuousGoodMass(W,t) is the Gibbs mass of those starting configurations x whose total-variation distance to equilibrium at time t still exceeds 1/4, and discreteGoodMass(W,k) is the analogous Gibbs mass after k attempts. Part one: for every sequence of nonnegative times t_n with t_n/n^(2/3) tending to 0, and every δ>0, the disorder probability that |continuousGoodMass(W,t_n) − 1| ≥ δ tends to 0 as n→∞. Part two: for every sequence of natural numbers k_n with k_n/n^(5/3) tending to 0, and every δ>0, the disorder probability that |discreteGoodMass(W,k_n) − 1| ≥ δ tends to 0. Thus with high probability, for such short times, almost all Gibbs mass lies on initial states that are still farther than 1/4 from equilibrium. The statement is admitted without proof in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CriticalSK.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CriticalSK.lean; bytes 4171..4948
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_CriticalSK

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory Filter

namespace CriticalSK

/-- For deterministic nonnegative times `o(n^(2/3))` and attempt counts `o(n^(5/3))`,
the Gibbs mass of obstructed initial states tends to one in disorder probability. -/
theorem realized_equilibrium_initial_states :
    (∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) →
      Tendsto (fun n => t n / (n : ℝ) ^ ((2 : ℝ) / 3)) atTop (𝓝 0) →
      ∀ δ : ℝ, 0 < δ →
        Tendsto (fun n => (disorderLaw n {W |
          δ ≤ |continuousGoodMass W (t n) - 1|}).toReal) atTop (𝓝 0)) ∧
    (∀ k : ℕ → ℕ,
      Tendsto (fun n => (k n : ℝ) / (n : ℝ) ^ ((5 : ℝ) / 3)) atTop (𝓝 0) →
      ∀ δ : ℝ, 0 < δ →
        Tendsto (fun n => (disorderLaw n {W |
          δ ≤ |discreteGoodMass W (k n) - 1|}).toReal) atTop (𝓝 0)) := by
  sorry

end CriticalSK
end
end OAI
