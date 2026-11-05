-- Prove2me | Theorems.Thm_LiquidWelfareFPA_lemma_4_1
-- name    : LiquidWelfareFPA.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:35:31.99224+00:00
-- url     : https://prove2.me/theorems/67d216f1-afd7-4fe3-a32e-7c6210349478
-- title:
--   Lemma 4.1 — $\sup_\mu\hat U_i(\mu)\ge\min\{\frac{1-\lambda}{\lambda}\mathrm{LW}^*_i,\,c(\lambda)\lambda\mathrm{LW}^*_i-c(\lambda)\sum_{O_i}p_t\}-1$
-- statement:
--   Consider an outcome of $T$ sequential first-price auctions with prices $p_t$, nonnegative budgets $B_i$ and any tie rule for the benchmark. Fix a player $i$ and a set of rounds $O\subseteq[T]$, and put $\mathrm{LW}^*_i=\min\{B_i,\sum_{t\in O}v_{it}\}$. Let $c(\lambda)=-1/\ln(1-\lambda)$. Then for every $\lambda\in(0,1)$,
--
--   $$\sup_{\mu\in[0,1]}\hat U_i(\mu)\ \ge\ \min\Big\{\frac{1-\lambda}{\lambda}\,\mathrm{LW}^*_i,\ c(\lambda)\lambda\,\mathrm{LW}^*_i-c(\lambda)\sum_{t\in O}p_t\Big\}-1 .$$
--
--   In the paper $O=O_i$ is player $i$'s bundle in the allocation maximizing liquid welfare. The lemma lower-bounds the best-shading-multiplier benchmark by the player's share of the optimal liquid welfare, which is how the competitive-ratio assumption is turned into a welfare guarantee.
--
--   Differences from the source:
--   - generalization: O_i is player i's bundle in the allocation maximizing liquid welfare, LW*_i = min{B_i, Σ_{t∈O_i} v_it} → any set of rounds O ⊆ [T], with min{B_i, Σ_{t∈O} v_it} in place of LW*_i; reason: the proof uses only Σ_{t∈O_i} v_it ≥ LW*_i and B_i ≥ LW*_i; taking O = O_i gives the printed lemma
--   - encoding: values and prices of the auction; budgets, bids and the tie rule left implicit → an outcome of the first-price auction (values in [0,1], bids ≥ 0, winner any highest bidder, price = winner's bid), budgets B_i ≥ 0, any tie rule; d_it := 0 when n = 1; reason: the model of §3; the proof uses d_it ≤ p_t, which holds in it (p.7)
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, Lemma 4.1, p.7

import Mathlib
import Definitions.Def_LiquidWelfareFPA_IsTieRule
import Definitions.Def_LiquidWelfareFPA_bench
import Definitions.Def_LiquidWelfareFPA_cfun

namespace LiquidWelfareFPA

/-- **Lemma 4.1 (benchmark lower bound).**
Fikioris & Tardos, arXiv:2210.07502v4, Lemma 4.1, p.7: "Fix a player i, her values v_i1, …, v_iT,
and the price of the items p_1, …, p_T. Let O_i ⊆ [T] be the items that player i gets in the
allocation that maximizes the total liquid welfare. Let c(λ) = −1/ln(1−λ). Then for any
λ ∈ (0, 1), it holds that sup_{µ∈[0,1]} Û_i(µ) ≥ min{(1−λ)/λ LW*_i, c(λ)λLW*_i − c(λ)∑_{t∈O_i} p_t} − 1."

For every outcome `o` with nonnegative budgets, every tie rule `win`, every player `i`, every set
of rounds `O` and every `λ ∈ (0,1)`, with `LW*_i := min{B_i, ∑_{t∈O} v_it}`:
`sup_{µ∈[0,1]} Û_i(µ) ≥ min{(1−λ)/λ · LW*_i, c(λ)λ LW*_i − c(λ) ∑_{t∈O} p_t} − 1`.

**Formalization Note** The bundle `O` is arbitrary rather than the optimal one; the printed lemma
is the case `O = O_i`. The prices are those of the outcome, so `d_it ≤ p_t` holds. -/
theorem lemma_4_1 {n T : ℕ} (B : Fin n → ℝ) (hB : ∀ i, 0 ≤ B i) (o : Outcome n T)
    (win : Fin n → Fin T → ℝ → Prop) (hwin : IsTieRule o win) (i : Fin n)
    (O : Finset (Fin T)) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    min ((1 - lam) / lam * min (B i) (∑ t ∈ O, o.v i t))
        (cfun lam * lam * min (B i) (∑ t ∈ O, o.v i t) - cfun lam * ∑ t ∈ O, o.price t) - 1
      ≤ bench B o win i := by sorry

end LiquidWelfareFPA
