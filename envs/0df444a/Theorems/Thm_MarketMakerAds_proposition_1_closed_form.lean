-- Prove2me | Theorems.Thm_MarketMakerAds_proposition_1_closed_form
-- name    : MarketMakerAds.proposition_1_closed_form
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:33:36.91889+00:00
-- url     : https://prove2.me/theorems/6dbbd2b4-6717-4c8f-aa5b-e43ad1d01ef4
-- title:
--   Proposition 1, closed form (3) with (14)–(15) — buyers with $v\ge p_{\max}$ are indifferent at $p^*_M$
-- statement:
--   Let the auction clearing price $p$ have law $h$ with $p\le p_{\max}$ almost surely, mean $\mu_A$ and variance $\sigma_A^2$, and assume its negative part has a finite second moment. Then for every value $v\ge p_{\max}$ (a buyer who always wins the auction):
--
--   1. (eq. (14), mean-variance, any $\beta$) $U_A(v)=v-\mu_A-\beta\sigma_A^2$;
--   2. (eq. (14), CARA, $\alpha\ge0$) $U_A(v)=1-e^{-\alpha v}\,\mathbf E_p[e^{\alpha p}]$;
--   3. for $\beta\ge0$, resp. $\alpha>0$: $U_A(v)=U_{\mathrm{buy}}(v,p^*_M)$, with $p^*_M$ given by (3);
--   4. for $\beta\ge0$, resp. $\alpha>0$, and every price $p_M$:
--
--   $$
--   U_A(v)\le U_{\mathrm{buy}}(v,p_M)\iff p_M\le p^*_M ;
--   $$
--
--   5. for CARA with $\alpha>0$, $p^*_M\le p_{\max}$.
--
--   So $p^*_M$ is the highest Market-Maker price that buyers who always win the auction weakly prefer to it, which is how the paper derives the closed form (3). Parts 1–2 of Proposition 1 (equilibrium existence) are not part of this statement.
--
--   Differences from the source:
--   - generalization: a clearing-price density on $[0,\infty)$ with $p_{\max}$ the highest clearing price in its support → any law on $\mathbb R$ with $p\le p_{\max}$ almost surely whose negative part has a finite second moment; reason: only $p\le p_{\max}$ is used; the paper's law satisfies both hypotheses.
--   - reading: the restatement on p.37, $p^*_M=\frac1\alpha\mathbf E_p[e^{\alpha p}]$ → $p^*_M=\frac1\alpha\log\mathbf E_p[e^{\alpha p}]$ as in eq. (3), p.17; reason: the two printings disagree, and only the one with the logarithm follows from (14)–(15).
--   - reading: "the Market-Maker price $p_M$ must be at most $p^*_M$" → $U_A(v)\le U_{\mathrm{buy}}(v,p_M)$ iff $p_M\le p^*_M$, for every $v\ge p_{\max}$; reason: this is the comparison of (14) with (15) that the sentence draws.
--   - encoding: $\alpha\ge0$ → $\alpha>0$ in items 3–5; reason: (3) divides by $\alpha$ and is undefined at $\alpha=0$.
-- source:
--   Cohen, Désir, Korula, Sivan, Best of Both Worlds Ad Contracts, SSRN 3088600, Proposition 1, p.17, eq. (3); Appendix D, Proof of Proposition 1, p.37, eqs. (14)–(15); p.18 ("p*_M is naturally capped at p_max")

import Mathlib
import Definitions.Def_MarketMakerAds_UA
import Definitions.Def_MarketMakerAds_Ubuy
import Definitions.Def_MarketMakerAds_pStar

open MeasureTheory

namespace MarketMakerAds

/-- **Proposition 1, closed form (3), p.17, with (14)–(15), p.37.**
Cohen, Désir, Korula, Sivan, *Best of Both Worlds Ad Contracts*, SSRN 3088600, Proposition 1,
p.17, eq. (3) "p*_M = µ_A + β · σ²_A (Mean-variance model), (1/α) · log(E_p[e^{α·p}]) (CARA
model)", and its proof, Appendix D, p.37: "for v ≥ p_max, we have (v − p)⁺ = v − p for any
auction clearing price p … the utility of buyers with valuation v ≥ p_max if they choose the
auction is: U_A(v) = v − µ_A − β · σ²_A (Mean-variance model), 1 − e^{−α·v} · E_p[e^{α·p}]
(CARA model). (14)" … "for the Market-Maker contract to be (weakly) preferred relative to the
auction for buyers with valuation v ≥ p_max, the Market-Maker price p_M must be at most p*_M".

Let the clearing price have law `h` with `p ≤ p_max` almost surely. Then
1. (14), mean-variance: for `v ≥ p_max`, `U_A(v) = v − µ_A − β σ²_A`;
2. (14), CARA (`α ≥ 0`): for `v ≥ p_max`, `U_A(v) = 1 − e^{−αv} E[e^{αp}]`;
3. for `v ≥ p_max`, `U_A(v) = U_buy(v, p*_M)`: such buyers are indifferent at `p*_M`;
4. for `v ≥ p_max` and every `p_M`: `U_A(v) ≤ U_buy(v, p_M)` iff `p_M ≤ p*_M`;
5. for CARA, `p*_M ≤ p_max`.

**Formalization Note** Items 3–4 use `β ≥ 0`, `α > 0` (`IsAdmissible`; (3) divides by `α`). The
restatement on p.37 omits the `log`; (3) has it. `p_max` is any almost-sure upper bound of the
clearing price here. The negative part of the price has a finite second moment (the paper's
prices are nonnegative). Parts 1–2 of Proposition 1 (equilibrium existence) are not stated. -/
theorem proposition_1_closed_form (h : Measure ℝ) [IsProbabilityMeasure h]
    (hneg : Integrable (fun p => (max (-p) 0) ^ 2) h) (pmax : ℝ)
    (h_le : ∀ᵐ p ∂h, p ≤ pmax) :
    (∀ β v : ℝ, pmax ≤ v →
      UA (.meanVariance β) h v = v - (∫ p, p ∂h) - β * ∫ p, (p - ∫ q, q ∂h) ^ 2 ∂h) ∧
    (∀ α v : ℝ, 0 ≤ α → pmax ≤ v →
      UA (.cara α) h v = 1 - Real.exp (-(α * v)) * ∫ p, Real.exp (α * p) ∂h) ∧
    (∀ m : RiskModel, m.IsAdmissible → ∀ v : ℝ, pmax ≤ v → UA m h v = Ubuy m v (pStar m h)) ∧
    (∀ m : RiskModel, m.IsAdmissible → ∀ v pM : ℝ, pmax ≤ v →
      (UA m h v ≤ Ubuy m v pM ↔ pM ≤ pStar m h)) ∧
    (∀ α : ℝ, 0 < α → pStar (.cara α) h ≤ pmax) := by sorry

end MarketMakerAds
