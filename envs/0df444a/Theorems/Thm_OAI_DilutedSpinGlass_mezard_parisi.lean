-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_mezard_parisi
-- name    : OAI.DilutedSpinGlass.mezard_parisi
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:34.266176+00:00
-- url     : https://prove2.me/theorems/9a256cd8-1dd2-4bc3-8418-4df0042d4328
-- statement:
--   The theorem states that for every model of a diluted p-spin glass with Ising spins in {+1,-1} that satisfies the standing admissibility hypotheses, the free-energy density F_N converges, as N tends to infinity, to a variational value, so existence of the thermodynamic limit is part of the conclusion. A model consists of a density α ≥ 0, a probability law on interaction samples (θ, a, b, f), where θ is a real function on spin configurations in {±1}^p, a and b are reals and f assigns to each of the p slots a real function on spins, and a probability law for the external field on ℝ. Admissibility means: p is even and at least 2; α > 0; ‖θ‖ = max_s |θ(s)| and |h| are integrable under the disorder and field laws; almost surely a > 0 and, for every configuration s, exp θ(s) = a(1 + b ∏_l f_l(s_l)) with |b ∏_l f_l(s_l)| < 1; the functions f_1,…,f_p are independent and identically distributed, b is independent of the vector f, every power (−b)^n with n ≥ 1 is integrable, and E[(−b)^n] ≥ 0. No boundedness of interactions, fields or messages is added. F_N is (1/N) times the expectation of log Σ_σ exp(−H), where the number k of interactions is Poisson with mean αN, the k interactions are independent disorder samples, the N fields are independent field samples, and each interaction is placed on p index choices in {1,…,N} (repetitions allowed) averaged uniformly over all choices; here the log-weight of σ is Σ_j θ_j(σ at the chosen indices) + Σ_i h_i σ_i. The limit is the infimum over depths r ≥ 0 of φ_r, itself the infimum, over a nested law ζ in the r-fold hierarchy of probability measures (each level with the weak topology and its Borel σ-field) and exponents 0 < m_1 < … < m_r < 1, of the cavity functional B_r. B_r equals log 2 plus the Poisson(αp)-averaged expectation of the site term, a logarithm of an average over spin ε of exp(hε + Σ_j message_j(ε)), minus α(p−1) times the expectation of the log of the edge weight, with both terms evaluated through iterated log power-means in the exponents m_i.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DilutedSpin.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DilutedSpin.lean; bytes 6529..6828
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_DilutedSpin

namespace OAI

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace DilutedSpinGlass

attribute [local instance] _root_.OAI.DilutedSpinGlass.instMeasurableSpaceCarrier_challenge

attribute [local instance] _root_.OAI.DilutedSpinGlass.instBorelSpaceCarrier_challenge

/-- main:theorem. No boundedness of interactions, fields, or messages is added.
Existence of the thermodynamic limit is part of this convergence assertion. -/
theorem mezard_parisi {p : ℕ} (M : Model p) (hM : Admissible M) :
    Tendsto (pressure M) atTop (𝓝 (variationalValue M)) := by
  sorry

end DilutedSpinGlass
end OAI
