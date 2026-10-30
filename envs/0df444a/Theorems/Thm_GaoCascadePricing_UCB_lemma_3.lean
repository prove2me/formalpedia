-- Prove2me | Theorems.Thm_GaoCascadePricing_UCB_lemma_3
-- name    : GaoCascadePricing.UCB.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T08:16:28.68699+00:00
-- url     : https://prove2.me/theorems/47d45335-8ff8-4cea-ac43-390a22f332e9
-- title:
--   Lemma 3 — Probability of the good estimation event
-- statement:
--   Fix a positive finite market, any resolution of UCB-Cascade's unspecified choices, and any valid stationary cascade. At every deterministic calendar time $t\ge1$, the simultaneous good estimation event satisfies
--   $$\Pr(\overline A_t)\ge 1-\frac{4J(K+1)}{t^3}.$$
--   Here $A_t$ is the union of the non-strict absolute-error comparisons with uncapped square-root radii, over every product-price click and purchase parameter and every nonterminal continuation parameter. Unavailable zero-count comparisons are absent. The probability is unconditional under the complete trajectory law, including initialization.
--
--   Differences from the source:
--   - encoding: products 1 through J and price labels 1 through K → zero-based finite indices with positive J and K; reason: the finite index sets are in bijection and every feasible vector is retained
--   - reading: monetary price points → nonnegative real prices in strictly increasing order; reason: the standing economic price convention is made explicit
--   - encoding: expectation over customer movements and external policy randomization → normalized action PMFs and finite sums of products of conditional path weights; reason: the paper has finite action and observation spaces, so this is the exact finite-horizon law
--   - reading: keep testing and select a UCBOPT solution, without specifying the choices → every history-dependent randomized testing rule and every maximizing tie rule, fixed before the unknown parameters; reason: the statement must cover the full underspecified algorithm rather than a favorable choice
--   - encoding: calendar time t at least one → history length n with t=n+1; reason: counters contain exactly the observations before the decision
--   - reading: error radii with undefined zero denominators → a zero-count comparison contributes no bad event; reason: this extends the event to all deterministic times without conditioning on initialization
-- source:
--   Gao, Jasin, Najafi and Zhang (2022), Joint Learning and Optimization for Multi-Product Pricing (and Ranking) Under a General Cascade Click Model, DOI https://doi.org/10.1287/mnsc.2021.4246; published basis, supplied manuscript-paginated PDF; Lemma 3, PDF = printed p. 17; SHA256 e199fc0dfffccf57ac4a59ae46b7a8342a11c3dd3db189795d3a5028b566b1b6

import Definitions.Def_GaoCascadePricing_UCB_EstimationEvent

namespace GaoCascadePricing.UCB

theorem lemma_3 {J K : ℕ} (M : Market J K)
    (π : Policy J K) (hπ : IsUCBCascade M π)
    (θ : Cascade J K) (hθ : θ.Valid) (n : ℕ) :
    1 - 4 * (J : ℝ) * ((K : ℝ) + 1) / ((n : ℝ) + 1) ^ 3 ≤
      probability θ π (fun h : History J K n => ¬ BadEvent θ h) := by sorry

end GaoCascadePricing.UCB
