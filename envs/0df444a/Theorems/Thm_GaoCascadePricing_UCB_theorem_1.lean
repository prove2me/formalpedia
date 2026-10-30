-- Prove2me | Theorems.Thm_GaoCascadePricing_UCB_theorem_1
-- name    : GaoCascadePricing.UCB.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T08:15:49.652725+00:00
-- url     : https://prove2.me/theorems/268d5181-8d5a-499f-8076-b7e7eb3376a7
-- title:
--   Theorem 1 — The regret bound for UCB-Cascade
-- statement:
--   There exist positive constants $C_1,C_2$, chosen uniformly before the positive integers $J,K$, prices, algorithm choices, unknown probabilities and horizon, such that every resolution of the printed UCB-Cascade algorithm on every valid stationary general cascade and every positive integer horizon $T$ satisfies
--   $$\mathrm{Regret}(T;\theta)\le C_1q_KJK+C_2\min\!\left\{\frac1{\underline\beta},\frac1{1-\overline\beta},\frac1{\underline\beta(1-\overline\alpha)}\right\}q_KJ^2\sqrt{KT\ln T}.$$
--   The extrema range over all product-price pairs. Regret includes the testing rounds from period one, and initialization may never complete. The inequality uses extended nonnegative reals, with reciprocals of zero equal to infinity. The statement retains the printed minimum and all factors; it is the source claim even though an allowed unreachable-product instance disproves it.
--
--   Differences from the source:
--   - encoding: products 1 through J and price labels 1 through K → zero-based finite indices with positive J and K; reason: the finite index sets are in bijection and every feasible vector is retained
--   - reading: monetary price points → nonnegative real prices in strictly increasing order; reason: the standing economic price convention is made explicit
--   - encoding: expectation over customer movements and external policy randomization → normalized action PMFs and finite sums of products of conditional path weights; reason: the paper has finite action and observation spaces, so this is the exact finite-horizon law
--   - reading: keep testing and select a UCBOPT solution, without specifying the choices → every history-dependent randomized testing rule and every maximizing tie rule, fixed before the unknown parameters; reason: the statement must cover the full underspecified algorithm rather than a favorable choice
--   - reading: positive constants independent of theta → positive constants quantified before J, K, the market, policy, theta and T; reason: the uniform reading of the advertised rate prevents instance-dependent constants
--   - reading: reciprocals undefined at zero → nonnegative extended reciprocals with 1/0=infinity and 0 times infinity=0; reason: all probability endpoints remain in the domain and every finite-defined expression agrees
--   - encoding: finite nonnegative expected regret → its canonical embedding using ENNReal.ofReal; reason: finite normalized trajectory expectations and a true finite maximum make regret nonnegative
-- source:
--   Gao, Jasin, Najafi and Zhang (2022), Joint Learning and Optimization for Multi-Product Pricing (and Ranking) Under a General Cascade Click Model, DOI https://doi.org/10.1287/mnsc.2021.4246; published basis, supplied manuscript-paginated PDF; Theorem 1, PDF = printed p. 16; SHA256 e199fc0dfffccf57ac4a59ae46b7a8342a11c3dd3db189795d3a5028b566b1b6

import Definitions.Def_GaoCascadePricing_UCB_Algorithm

namespace GaoCascadePricing.UCB

theorem theorem_1 :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (J K : ℕ) (M : Market J K) (π : Policy J K), IsUCBCascade M π →
      ∀ (θ : Cascade J K), θ.Valid → ∀ (T : ℕ), 0 < T →
        ENNReal.ofReal (regret M θ π T) ≤
          ENNReal.ofReal (C₁ * largestPrice M * J * K) +
          ENNReal.ofReal C₂ * regretCoefficient θ *
          ENNReal.ofReal (largestPrice M * (J : ℝ) ^ 2 *
            Real.sqrt ((K : ℝ) * T * Real.log T)) := by sorry

end GaoCascadePricing.UCB
