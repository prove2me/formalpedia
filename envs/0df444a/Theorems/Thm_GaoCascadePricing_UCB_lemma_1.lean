-- Prove2me | Theorems.Thm_GaoCascadePricing_UCB_lemma_1
-- name    : GaoCascadePricing.UCB.lemma_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T08:14:34.213775+00:00
-- url     : https://prove2.me/theorems/bbf06a9b-2811-4042-a1ee-c3900a4eea17
-- title:
--   Lemma 1 — Single-parameter revenue perturbation
-- statement:
--   Let $\theta$ and $\theta'$ be two valid general cascades on the same positive finite market, and fix a price vector $p$ and a product $i$. All parameters at other products agree. Exactly one of the four selected parameters $\beta_{i,k(i,p)},\alpha_{i,k(i,p)},\gamma_i,\zeta_i$ changes, with absolute change $\epsilon$. Then
--   $$|\rho(p;\theta)-\rho(p;\theta')|\le\|p\|_\infty\Bigl(\prod_{j<i}\mu_j(p_j;\theta')\Bigr)\epsilon.$$
--   The primed reach product and coefficient one are retained. Prices at product $i$ that are not used in $p$ impose no further condition.
--
--   Differences from the source:
--   - encoding: products 1 through J and price labels 1 through K → zero-based finite indices with positive J and K; reason: the finite index sets are in bijection and every feasible vector is retained
--   - reading: monetary price points → nonnegative real prices in strictly increasing order; reason: the standing economic price convention is made explicit
--   - encoding: the absolute difference epsilon of the unique changed parameter → the absolute difference of one selected coordinate in a four-element parameter index; reason: the nonzero-change premise and equality of the other three coordinates express exactly one change
-- source:
--   Gao, Jasin, Najafi and Zhang (2022), Joint Learning and Optimization for Multi-Product Pricing (and Ranking) Under a General Cascade Click Model, DOI https://doi.org/10.1287/mnsc.2021.4246; published basis, supplied manuscript-paginated PDF; Lemma 1, PDF = printed p. 16; SHA256 e199fc0dfffccf57ac4a59ae46b7a8342a11c3dd3db189795d3a5028b566b1b6

import Definitions.Def_GaoCascadePricing_UCB_Market

namespace GaoCascadePricing.UCB

theorem lemma_1 {J K : ℕ} (M : Market J K)
    (θ θ' : Cascade J K) (hθ : θ.Valid) (hθ' : θ'.Valid)
    (p : Action J K) (i : Fin J) (a : Fin 4)
    (hother : ∀ j, j ≠ i →
      (∀ k, θ.beta j k = θ'.beta j k ∧ θ.alpha j k = θ'.alpha j k) ∧
      θ.gamma j = θ'.gamma j ∧ θ.zeta j = θ'.zeta j)
    (hsame : ∀ b : Fin 4, b ≠ a → parameter θ p i b = parameter θ' p i b)
    (hdiff : parameter θ p i a ≠ parameter θ' p i a) :
    |revenue M θ p - revenue M θ' p| ≤
      priceNorm M p * reach θ' p i * |parameter θ p i a - parameter θ' p i a| := by sorry

end GaoCascadePricing.UCB
