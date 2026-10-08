-- Prove2me | Theorems.Thm_HedgeInv_Value_proposition5_hedge_value
-- name    : HedgeInv.Value.proposition5_hedge_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:19:00.032091+00:00
-- url     : https://prove2.me/theorems/a81bb2fd-20a5-47a3-944d-c9e5bf638326
-- title:
--   Proposition 5, p. 111 — for concave differentiable $u$, $\frac{d}{d\alpha}\mathbb E[u(\Pi_H(I,\alpha))]|_{\alpha=0}\ge 0$
-- statement:
--   Consider a newsvendor who orders $I$ units now and sells at a future date $T$ against a demand $D=a+bS_T+\varepsilon'$ that is correlated with the price $S_T$ of a traded asset. In the scaled units of Gaur and Seshadri, the firm has scaled wealth $W$, demand parameters $a$ and $b>0$, an order quantity $I>\max\{a,0\}$ and a scaled unit cost $c_1$ with $0<c_1$ and $c_1b<1$ (the scaled form of $p>ce^{rT}>s$). The price $S_T$ has law $\nu$, the scaled forecast error $\varepsilon=\varepsilon'/b$ has law $G$, both probability measures on $\mathbb R$; $S_T$ and $\varepsilon$ are independent, $\mathbb E[\varepsilon]=0$ and $\mathbb E[\varepsilon^2]<\infty$.
--
--   The firm can short an amount $\alpha$ of a portfolio with time-$T$ payoff $X_T=\varphi(S_T)$, where $\varphi$ is nondecreasing, measurable and $\nu$-integrable, and whose forward price $X_0e^{rT}$ makes it a fair gamble, $\mathbb E[X_T-X_0e^{rT}]=0$ (12). Its wealth is then
--   $$W+\Pi_H(I,\alpha)=W+\min\{S_T+\varepsilon,(I-a)/b\}-c_1I-\alpha X_T+\alpha X_0e^{rT}.$$
--
--   **Proposition 5.** For any concave and differentiable utility function $u$,
--   $$\frac{d}{d\alpha}\mathbb E[u(\Pi_H(I,\alpha))]\Big|_{\alpha=0}\ \ge\ 0.$$
--   Precisely: suppose that for some $\delta>0$ the utility $u(W+\Pi_H(I,\alpha))$ is integrable at $\alpha=-\delta,0,\delta$, and that $u'(W+\Pi_H(I,0))$ is integrable. Then $\alpha\mapsto\mathbb E[u(\Pi_H(I,\alpha))]$ is differentiable at $\alpha=0$ and its derivative there is nonnegative.
--
--   The result says that a risk-averse newsvendor, for any fixed order quantity, gains (to first order) from taking a small short position in a fair hedge that is increasing in the asset price: hedging never hurts at the margin.
--
--   **Formalization Note** The conclusion asserts that the derivative exists (two-sided) and is nonnegative, so it cannot hold through a default value of the derivative. The two integrability assumptions are regularity conditions the paper uses silently when it differentiates under the expectation and writes $\mathbb E[u'(\cdot)]$ as a factor. "Increasing" for $X_T$ is read as nondecreasing. Expectations are integrals against the product law $\nu\otimes G$. No monotonicity of $u$ is assumed, exactly as printed.
-- source:
--   Gaur & Seshadri, Hedging Inventory Risk Through Market Instruments, Manuf. Serv. Oper. Manag. 7(2) (2005), p. 111, Proposition 5, display (15); setting (11), (12), (14) pp. 110–111; proof p. 118

import Mathlib
import Definitions.Def_HedgeInv_Value_Model
open MeasureTheory

namespace HedgeInv.Value

/-- Proposition 5, p. 111 (Gaur & Seshadri 2005), display (15): for any concave and differentiable
utility `u`, `d/dα E[u(Π_H(I, α))]|_{α=0} ≥ 0`. The derivative exists (two-sided) and is
nonnegative. -/
theorem proposition5_hedge_value
    (ν G : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure G]
    (hG_mean : ∫ e, e ∂G = 0) (hG_L2 : MemLp id 2 G)
    (W a b c₁ I : ℝ) (hb : 0 < b) (hI : max a 0 < I) (hc₁ : 0 < c₁) (hc₁b : c₁ * b < 1)
    (φ : ℝ → ℝ) (hφ_mono : Monotone φ) (hφ_meas : Measurable φ) (hφ_int : Integrable φ ν)
    (x0r : ℝ) (h12 : ∫ s, φ s ∂ν = x0r)
    (u : ℝ → ℝ) (hu_conc : ConcaveOn ℝ Set.univ u) (hu_diff : Differentiable ℝ u)
    (δ : ℝ) (hδ : 0 < δ)
    (hint : ∀ α ∈ ({-δ, 0, δ} : Set ℝ),
      Integrable (fun p : ℝ × ℝ => u (HedgeInv.Order.hedgedPayoff W a b c₁ φ x0r I α p.1 p.2)) (ν.prod G))
    (hint_du : Integrable (fun p : ℝ × ℝ => deriv u (unhedgedPayoff W a b c₁ I p.1 p.2)) (ν.prod G)) :
    ∃ D : ℝ, HasDerivAt (fun α => HedgeInv.Order.expUtil ν G u W a b c₁ φ x0r I α) D 0 ∧ 0 ≤ D := by sorry

end HedgeInv.Value
