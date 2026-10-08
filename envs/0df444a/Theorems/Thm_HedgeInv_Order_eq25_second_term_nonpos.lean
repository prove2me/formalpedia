-- Prove2me | Theorems.Thm_HedgeInv_Order_eq25_second_term_nonpos
-- name    : HedgeInv.Order.eq25_second_term_nonpos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:22.725882+00:00
-- url     : https://prove2.me/theorems/c3c800f5-7b3a-4a42-aa45-87761c158c8b
-- title:
--   Proof of Proposition 7, p. 119 — (1/b)R_A(Π₀)u′(Π₀)Pr{ε > (I − a)/b − S_T}∂Π/∂α has nonpositive mean
-- statement:
--   Work in the hedged newsvendor model under its standing assumptions, with a utility $u$ in the class of Proposition 7. Fix $I>\max\{a,0\}$ and $\alpha\ge0$. Let $\Pi_0=W+(I-a)/b-c_1I-\alpha X_T+\alpha X_0e^{rT}$ be the payoff on the sell-out event, and $\partial\Pi/\partial\alpha=X_0e^{rT}-X_T$. Then
--   $$E\Big[\frac1b\,R_A(\Pi_0)\,u'(\Pi_0)\,\Pr\Big\{\varepsilon>\frac{I-a}{b}-S_T\ \Big|\ S_T\Big\}\,\big(X_0e^{rT}-X_T\big)\Big]\ \le\ 0,$$
--   where the probability is taken over $\varepsilon\sim G$ at fixed $S_T$.
--
--   This quantity enters (25) with a minus sign, so its contribution to $\partial^2E[u(\Pi)]/\partial I\partial\alpha$ is nonnegative.
--
--   **Formalization Note.** The paper says this term "is negative". The weak inequality is stated: the term vanishes, for example, when the hedge is constant. The paper writes $\Pi_0=(I-a)/b-c_1I-\alpha X_T+\alpha X_0$. Here the payoff (14) is used, which includes $W$ and the compounding factor, so $\Pi_0$ is (14) evaluated on the sell-out event.
-- source:
--   Gaur & Seshadri, Hedging Inventory Risk Through Market Instruments, Manuf. Serv. Oper. Manag. 7(2) (2005), p. 119, Appendix, proof of Proposition 7, display (25)

import Mathlib
import Definitions.Def_HedgeInv_Order_Model

namespace HedgeInv.Order

open MeasureTheory

/-- Proof of Proposition 7, p. 119: with `Π₀(s)` the payoff on the sell-out event
`{ε > (I − a)/b − S_T}`, the second term of (25) without its minus sign,
`E[(1/b) R_A(Π₀) u′(Π₀) Pr{ε > (I − a)/b − S_T} · ∂Π/∂α]`, is nonpositive, for a DARA/CARA and
DAP utility and `α ≥ 0`. -/
theorem eq25_second_term_nonpos (ν G : Measure ℝ) (u : ℝ → ℝ) (W a b c₁ : ℝ) (φ : ℝ → ℝ)
    (x0r I α : ℝ)
    (hstd : StandingAssumptions ν G b c₁ φ x0r) (hu : IsDARADAPUtility u)
    (hI : max a 0 < I) (hα : 0 ≤ α) :
    ∫ s, (1 / b) * MDPFinance.FinancialMarkets.arrowPrattCoefficient u
        (payoffSoldOut W a b c₁ φ x0r I α s)
      * deriv u (payoffSoldOut W a b c₁ φ x0r I α s)
      * (G {e | (I - a) / b - s < e}).toReal * (x0r - φ s) ∂ν ≤ 0 := by sorry

end HedgeInv.Order
