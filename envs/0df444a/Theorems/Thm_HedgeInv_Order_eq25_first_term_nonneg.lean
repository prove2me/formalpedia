-- Prove2me | Theorems.Thm_HedgeInv_Order_eq25_first_term_nonneg
-- name    : HedgeInv.Order.eq25_first_term_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:33.40141+00:00
-- url     : https://prove2.me/theorems/9d8813a5-5e33-4af6-a295-a41fed0df169
-- title:
--   Proof of Proposition 7, p. 119 — the first term of (25) is nonnegative
-- statement:
--   Work in the hedged newsvendor model under its standing assumptions, with a utility $u$ in the class of Proposition 7 and the $\bar\alpha$-condition. Fix $I>\max\{a,0\}$ and $\alpha\in[0,\bar\alpha]$, and assume $\varepsilon\mapsto u''(\Pi_H(I,\alpha))$ is $G$-integrable at every $S_T=s$. Write $\partial\Pi/\partial\alpha=X_0e^{rT}-X_T$. Then the first term of (25) is nonnegative:
--   $$E\Big[-c_1\,E_\varepsilon\big[u''(\Pi_H(I,\alpha))\,\big|\,S_T\big]\cdot\big(X_0e^{rT}-X_T\big)\Big]\ \ge\ 0.$$
--
--   Together with the sign of the second term, this gives $\partial^2E[u(\Pi)]/\partial I\partial\alpha\ge0$.
-- source:
--   Gaur & Seshadri, Hedging Inventory Risk Through Market Instruments, Manuf. Serv. Oper. Manag. 7(2) (2005), p. 119, Appendix, proof of Proposition 7, display (25)

import Mathlib
import Definitions.Def_HedgeInv_Order_Model

namespace HedgeInv.Order

open MeasureTheory

/-- Proof of Proposition 7, p. 119: the first term of (25),
`E[−c₁ E_ε[u″(Π) | S_T] · ∂Π/∂α]` with `∂Π/∂α = X₀e^{rT} − X_T = x0r − φ(S_T)`, is nonnegative,
for a DARA/CARA and DAP utility, `α ∈ [0, ᾱ]` and `I > max{a, 0}`. -/
theorem eq25_first_term_nonneg (ν G : Measure ℝ) (u : ℝ → ℝ) (W a b c₁ : ℝ) (φ : ℝ → ℝ)
    (x0r αbar I α : ℝ)
    (hstd : StandingAssumptions ν G b c₁ φ x0r) (hu : IsDARADAPUtility u)
    (hαbar : AlphaBarCond G W a b c₁ φ x0r αbar)
    (hI : max a 0 < I) (hα : α ∈ Set.Icc (0 : ℝ) αbar)
    (hint : ∀ s, Integrable (fun e => deriv (deriv u) (hedgedPayoff W a b c₁ φ x0r I α s e)) G) :
    0 ≤ ∫ s, (-c₁ * ∫ e, deriv (deriv u) (hedgedPayoff W a b c₁ φ x0r I α s e) ∂G)
      * (x0r - φ s) ∂ν := by sorry

end HedgeInv.Order
