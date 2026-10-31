-- Prove2me | Theorems.Thm_MarketMakerAds_corollary_2
-- name    : MarketMakerAds.corollary_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:34:30.601096+00:00
-- url     : https://prove2.me/theorems/a8ccd876-0046-4589-afe6-f56a51e2cf91
-- title:
--   Corollary 2 — buyers below $p_{\max}$ strictly prefer the auction (corrected: comparison with buying the contract)
-- statement:
--   Let the auction clearing price have law $h$ whose negative part has a finite second moment, with top of support $p_{\max}$: $p\le p_{\max}$ almost surely and $h\big((v,\infty)\big)>0$ for every $v<p_{\max}$. Offer the Market-Maker contract at $p^*_M$, with $\beta\ge0$, resp. $\alpha>0$. Then:
--
--   1. for every $v<p_{\max}$, buying is strictly worse than the auction: $U_{\mathrm{buy}}(v,p^*_M)<U_A(v)$;
--   2. for every $v\ge p_{\max}$, the buyer is indifferent: $U_A(v)=U_{\mathrm{buy}}(v,p^*_M)$;
--   3. consequently the buyers who opt for the contract at $p^*_M$ (with $p^*_M\le v$ and ties to the Market-Maker) are exactly those with
--
--   $$
--   v\ge\max\big(p_{\max},\,p^*_M\big).
--   $$
--
--   In particular at most the buyers who always win the auction move to the contract.
--
--   Differences from the source:
--   - correction: "buyers with valuations $v<p_{\max}$ strictly prefer to participate in the auction", compared with $U_M=(v-p^*_M)^+$ of eq. (2) → $U_{\mathrm{buy}}(v,p^*_M)<U_A(v)$, the comparison with the utility $v-p^*_M$ (resp. $1-e^{-\alpha(v-p^*_M)}$) of buying; reason: the printed claim is false: the buyer with $v=0$ has $U_A(0)=0=(0-p^*_M)^+$ for every law on $[0,\infty)$, so it is indifferent, not strictly better off in the auction.
--   - reading: "weakly prefer to choose the Market-Maker contract" → $U_A(v)=U_{\mathrm{buy}}(v,p^*_M)$, plus the resulting buyer set under the purchase rule with ties to the Market-Maker; reason: p.18: "all the buyers with valuations $v\ge p_{\max}$ are indifferent … we assume that such indifferent buyers opt for the Market-Maker contract".
--   - generalization: a clearing-price density on $[0,\infty)$ → any law on $\mathbb R$ with top of support $p_{\max}$ whose negative part has a finite second moment, with no assumption at $p_{\max}$; reason: the paper's law satisfies these hypotheses.
--   - encoding: $\alpha\ge0$ → $\alpha>0$; reason: $p^*_M$ is undefined at $\alpha=0$.
-- source:
--   Cohen, Désir, Korula, Sivan, Best of Both Worlds Ad Contracts, SSRN 3088600, Corollary 2, p.18; Appendix D, p.37, eqs. (14)–(15)

import Mathlib
import Definitions.Def_MarketMakerAds_buysMM
import Definitions.Def_MarketMakerAds_pStar

open MeasureTheory

namespace MarketMakerAds

/-- **Corollary 2, p.18 (corrected: comparison with buying the contract).**
Cohen, Désir, Korula, Sivan, *Best of Both Worlds Ad Contracts*, SSRN 3088600, Corollary 2, p.18:
"When offering a Market-Maker contract at price p*_M, buyers with valuations v < p_max strictly
prefer to participate in the auction in P2, whereas buyers with valuations v ≥ p_max weakly prefer
to choose the Market-Maker contract in P1."

Let the clearing price have law `h`, with top of support `p_max` (`p ≤ p_max` a.s. and
`h(v, ∞) > 0` for every `v < p_max`), and let `β ≥ 0`, resp. `α > 0`. Then
1. for `v < p_max`, `U_buy(v, p*_M) < U_A(v)`: buying at `p*_M` is strictly worse than the auction;
2. for `v ≥ p_max`, `U_A(v) = U_buy(v, p*_M)`: such buyers are indifferent;
3. hence the buyers who opt for the contract at `p*_M` are exactly those with
   `v ≥ max(p_max, p*_M)`.

**Formalization Note** The printed strict clause compares the auction with
`U_M = (v − p*_M)⁺` of eq. (2) and is false (the buyer with `v = 0` gets `0` from both). The
statement compares with the utility of buying, `v − p*_M` (resp. `1 − e^{−α(v − p*_M)}`), as the
proof of Proposition 1 does in (14)–(15), p.37. Item 3 uses the purchase rule `buysMM`
(ties to the Market-Maker, `p_M ≤ v`). -/
theorem corollary_2 (m : RiskModel) (hm : m.IsAdmissible) (h : Measure ℝ) [IsProbabilityMeasure h]
    (hneg : Integrable (fun p => (max (-p) 0) ^ 2) h) (pmax : ℝ)
    (h_le : ∀ᵐ p ∂h, p ≤ pmax) (h_top : ∀ v < pmax, 0 < h (Set.Ioi v)) :
    (∀ v : ℝ, v < pmax → Ubuy m v (pStar m h) < UA m h v) ∧
    (∀ v : ℝ, pmax ≤ v → UA m h v = Ubuy m v (pStar m h)) ∧
    (∀ v : ℝ, buysMM m h (pStar m h) v ↔ max pmax (pStar m h) ≤ v) := by sorry

end MarketMakerAds
