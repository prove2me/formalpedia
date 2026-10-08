-- Prove2me | Theorems.Thm_HedgeInv_Order_dara_third_deriv_nonneg
-- name    : HedgeInv.Order.dara_third_deriv_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:21.420535+00:00
-- url     : https://prove2.me/theorems/ec193148-dbb3-4008-9c02-1743612a0a07
-- title:
--   §3.2, p. 111 — DARA or CARA implies u‴ ≥ 0
-- statement:
--   Let $u:\mathbb R\to\mathbb R$ be three times continuously differentiable with $u'(w)>0$ and $u''(w)<0$ for all $w$. Suppose the Arrow–Pratt absolute risk aversion $R_A(w)=-u''(w)/u'(w)$ is nonincreasing in $w$; this covers decreasing (DARA) and constant (CARA) risk aversion. Then
--   $$u'''(w)\ \ge\ 0\qquad\text{for all } w\in\mathbb R.$$
--
--   Equivalently, $|u''|$ is nonincreasing: risk-averse utilities with nonincreasing absolute risk aversion are prudent. The proof of Proposition 7 uses this fact.
--
--   **Formalization Note.** The paper's "increasing concave utility" is taken as $u'>0$ and $u''<0$ on all of $\mathbb R$ (strict concavity), and $C^3$ regularity is assumed so that $u'''$ exists.
-- source:
--   Gaur & Seshadri, Hedging Inventory Risk Through Market Instruments, Manuf. Serv. Oper. Manag. 7(2) (2005), p. 111, §3.2

import Mathlib
import Definitions.Def_MDPFinance_FinancialMarkets_Utility

namespace HedgeInv.Order

/-- §3.2, p. 111: for an increasing, strictly concave, three times continuously differentiable
utility `u : ℝ → ℝ` with constant or decreasing absolute risk aversion `R_A = −u″/u′`,
`u‴(w) ≥ 0` for every `w`. -/
theorem dara_third_deriv_nonneg (u : ℝ → ℝ) (hu : ContDiff ℝ 3 u)
    (hu1 : ∀ w, 0 < deriv u w) (hu2 : ∀ w, deriv (deriv u) w < 0)
    (hDARA : Antitone (MDPFinance.FinancialMarkets.arrowPrattCoefficient u)) :
    ∀ w, 0 ≤ deriv (deriv (deriv u)) w := by sorry

end HedgeInv.Order
