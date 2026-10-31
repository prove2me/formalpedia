-- Prove2me | Theorems.Thm_MarketMakerAds_theorem_2
-- name    : MarketMakerAds.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:34:22.163042+00:00
-- url     : https://prove2.me/theorems/2d971072-9927-4691-80c9-61ab81bf9b31
-- title:
--   Theorem 2 (Market-Maker Equilibrium Monotonicity)
-- statement:
--   Let the auction clearing price have law $h$, whose negative part has a finite second moment, let $p_M$ be any Market-Maker price, and take the mean-variance model with $\beta\ge0$ or the CARA model with $\alpha\ge0$. If a buyer with value $\tilde v$ opts for the Market-Maker contract, that is,
--
--   $$
--   p_M\le\tilde v\quad\text{and}\quad U_A(\tilde v)\le U_{\mathrm{buy}}(\tilde v,p_M),
--   $$
--
--   then every buyer with value $v\ge\tilde v$ opts for it too.
--
--   So the buyers of the contract form an up-set of values: low-value buyers, who are protected from high prices by losing the auction, prefer the auction.
--
--   Differences from the source:
--   - generalization: "in any two-period equilibrium induced by a Market-Maker price $p_M$" → for every law $h$ of the clearing price; reason: the proof (p.34) uses nothing about the equilibrium beyond the clearing-price law it induces.
--   - generalization: continuous distribution of valuations with a clearing-price density (p.34) → any probability law on $\mathbb R$ whose negative part has a finite second moment; reason: every law on $[0,\infty)$ satisfies the hypothesis.
--   - reading: "purchase the Market-Maker contract" → $p_M\le v$ and $U_A(v)\le U_{\mathrm{buy}}(v,p_M)$, ties to the Market-Maker; reason: the paper's buyer decision (p.10) with indifferent buyers opting for the contract (p.18); the positive part of eq. (2) means a buyer with $v<p_M$ does not buy.
-- source:
--   Cohen, Désir, Korula, Sivan, Best of Both Worlds Ad Contracts, SSRN 3088600, Theorem 2, p.16 (restated and proved in Appendix C, pp.34–36)

import Mathlib
import Definitions.Def_MarketMakerAds_buysMM

open MeasureTheory

namespace MarketMakerAds

/-- **Theorem 2 (Market-Maker Equilibrium Monotonicity), p.16.**
Cohen, Désir, Korula, Sivan, *Best of Both Worlds Ad Contracts*, SSRN 3088600, Theorem 2, p.16
(restated p.34): "Under both the CARA and Mean-variance models, in any two-period equilibrium
induced by a Market-Maker price p_M, if there exists a value ṽ such that buyers with valuation ṽ
purchase the Market-Maker contract in P1 (rather than waiting to participate in the auction in
P2), all buyers with valuations v ≥ ṽ will also purchase the Market-Maker contract in P1."

For every law `h` of the auction clearing price, every Market-Maker price `p_M` and every risk
model with `β ≥ 0` (resp. `α ≥ 0`): if a buyer with value `ṽ` (`vt`) buys the contract, so does every
buyer with value `v ≥ ṽ`.

**Formalization Note** "In any two-period equilibrium" is encoded as "for every clearing-price
law `h`": the proof (p.34) uses nothing about the equilibrium beyond the law of the clearing price
it induces. As in Remark 1 (p.16), the contract is assumed to deliver. `h` is any probability law on
`ℝ` whose negative part has a finite second moment; the paper assumes a density. -/
theorem theorem_2 (m : RiskModel) (hm : m.IsNonneg) (h : Measure ℝ) [IsProbabilityMeasure h]
    (hneg : Integrable (fun p => (max (-p) 0) ^ 2) h) (pM vt v : ℝ)
    (hbuy : buysMM m h pM vt) (hv : vt ≤ v) :
    buysMM m h pM v := by sorry

end MarketMakerAds
