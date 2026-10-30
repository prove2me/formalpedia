-- Prove2me | Theorems.Thm_GaoCascadePricing_UCB_lemma_2
-- name    : GaoCascadePricing.UCB.lemma_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T08:14:29.912991+00:00
-- url     : https://prove2.me/theorems/1ce98f9a-8d86-4441-b136-80eec1d16d7c
-- title:
--   Lemma 2 — All-parameter revenue perturbation
-- statement:
--   For every price vector $p$ and every two valid general cascades $\theta,\theta'$ on the same positive finite market,
--   $$|\rho(p;\theta)-\rho(p;\theta')|\le\|p\|_\infty\sum_{i=1}^J\Bigl(\prod_{j<i}\mu_j(p_j;\theta')\Bigr)\bigl(|\beta'_{i,k(i,p)}-\beta_{i,k(i,p)}|+|\alpha'_{i,k(i,p)}-\alpha_{i,k(i,p)}|+|\gamma'_i-\gamma_i|+|\zeta'_i-\zeta_i|\bigr).$$
--   Both models have zero terminal continuation parameters. There is no common-price restriction.
--
--   Differences from the source:
--   - encoding: products 1 through J and price labels 1 through K → zero-based finite indices with positive J and K; reason: the finite index sets are in bijection and every feasible vector is retained
--   - reading: monetary price points → nonnegative real prices in strictly increasing order; reason: the standing economic price convention is made explicit
--   - reading: the displayed index k in each product term → the price index selected by p at that product; reason: Lemma 1 and the proof identify k with k(i,p)
-- source:
--   Gao, Jasin, Najafi and Zhang (2022), Joint Learning and Optimization for Multi-Product Pricing (and Ranking) Under a General Cascade Click Model, DOI https://doi.org/10.1287/mnsc.2021.4246; published basis, supplied manuscript-paginated PDF; Lemma 2, PDF = printed p. 16; SHA256 e199fc0dfffccf57ac4a59ae46b7a8342a11c3dd3db189795d3a5028b566b1b6

import Definitions.Def_GaoCascadePricing_UCB_Market

open scoped BigOperators

namespace GaoCascadePricing.UCB

theorem lemma_2 {J K : ℕ} (M : Market J K)
    (θ θ' : Cascade J K) (hθ : θ.Valid) (hθ' : θ'.Valid) (p : Action J K) :
    |revenue M θ p - revenue M θ' p| ≤ priceNorm M p *
      ∑ i, reach θ' p i *
        (|θ'.beta i (p i) - θ.beta i (p i)| +
         |θ'.alpha i (p i) - θ.alpha i (p i)| +
         |θ'.gamma i - θ.gamma i| + |θ'.zeta i - θ.zeta i|) := by sorry

end GaoCascadePricing.UCB
