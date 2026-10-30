-- Prove2me | Theorems.Thm_GaoCascadePricing_UCB_lemma_4
-- name    : GaoCascadePricing.UCB.lemma_4
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T08:16:43.119993+00:00
-- url     : https://prove2.me/theorems/437a93b5-1aaa-4fe6-9c63-ea6b8cf4a0e9
-- title:
--   Lemma 4 — Conversion of estimated reach weights
-- statement:
--   Fix a positive finite market, a valid stationary cascade and any resolution of UCB-Cascade. For every initialized history of positive probability at calendar time $t$, and every given price vector $p$, let $u_{jt}$ be the sum of the four printed bonuses and let $\widehat\mu_{jt}$ and $\mu_{jt}$ be the empirical and true continuation probabilities at $p_j$. Then the source asserts
--   $$\sum_{j=1}^J\Bigl(\prod_{\ell<j}\widehat\mu_{\ell t}\Bigr)u_{jt}\le4J\sum_{j=1}^J\Bigl(\prod_{\ell<j}\mu_{\ell t}\Bigr)u_{jt}.$$
--   There is no good-event premise and $p$ need not maximize the objective. The zeta bonus remains uncapped. This is the printed assertion; the recorded source counterexample is not repaired in the target.
--
--   Differences from the source:
--   - encoding: products 1 through J and price labels 1 through K → zero-based finite indices with positive J and K; reason: the finite index sets are in bijection and every feasible vector is retained
--   - reading: monetary price points → nonnegative real prices in strictly increasing order; reason: the standing economic price convention is made explicit
--   - encoding: expectation over customer movements and external policy randomization → normalized action PMFs and finite sums of products of conditional path weights; reason: the paper has finite action and observation spaces, so this is the exact finite-horizon law
--   - reading: keep testing and select a UCBOPT solution, without specifying the choices → every history-dependent randomized testing rule and every maximizing tie rule, fixed before the unknown parameters; reason: the statement must cover the full underspecified algorithm rather than a favorable choice
--   - encoding: a period with defined empirical estimates → an initialized public history of positive trajectory probability at time n+1; reason: this is the domain of the printed ratios on realizable histories and imposes no confidence condition
--   - reading: the shorthand true parameter theta_t → the fixed stationary true parameter theta; reason: the model has no time-varying environment
-- source:
--   Gao, Jasin, Najafi and Zhang (2022), Joint Learning and Optimization for Multi-Product Pricing (and Ranking) Under a General Cascade Click Model, DOI https://doi.org/10.1287/mnsc.2021.4246; published basis, supplied manuscript-paginated PDF; Lemma 4, PDF = printed p. 17; SHA256 e199fc0dfffccf57ac4a59ae46b7a8342a11c3dd3db189795d3a5028b566b1b6

import Definitions.Def_GaoCascadePricing_UCB_EstimationEvent

namespace GaoCascadePricing.UCB

theorem lemma_4 {J K : ℕ} (M : Market J K)
    (π : Policy J K) (hπ : IsUCBCascade M π)
    (θ : Cascade J K) (hθ : θ.Valid) (n : ℕ) (h : History J K n)
    (hpossible : 0 < historyWeight θ π h) (hinit : Initialized h) (p : Action J K) :
    weightedBonus (estimate h) h p ≤ 4 * (J : ℝ) * weightedBonus θ h p := by sorry

end GaoCascadePricing.UCB
