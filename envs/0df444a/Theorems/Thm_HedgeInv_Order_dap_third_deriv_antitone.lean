-- Prove2me | Theorems.Thm_HedgeInv_Order_dap_third_deriv_antitone
-- name    : HedgeInv.Order.dap_third_deriv_antitone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:22.627333+00:00
-- url     : https://prove2.me/theorems/c0934076-5dc9-431d-8c78-d06f4ce7b3c3
-- title:
--   §3.2, p. 111 — constant or decreasing absolute prudence implies u‴ is decreasing
-- statement:
--   Let $u:\mathbb R\to\mathbb R$ be three times continuously differentiable with $u'(w)>0$ and $u''(w)<0$ for all $w$. Suppose the absolute prudence $P(w)=-u'''(w)/u''(w)$ is nonincreasing in $w$ (constant or decreasing absolute prudence). Then
--   $$w\mapsto u'''(w)\ \text{ is nonincreasing on } \mathbb R.$$
--
--   The proof of Proposition 7 uses this to show that $u'''$ of the hedged payoff decreases in the forecast error $\varepsilon$.
--
--   **Formalization Note.** The hypothesis $u'>0$ on all of $\mathbb R$ matters: without it, a utility with constant negative prudence would satisfy the other hypotheses and violate the conclusion.
-- source:
--   Gaur & Seshadri, Hedging Inventory Risk Through Market Instruments, Manuf. Serv. Oper. Manag. 7(2) (2005), p. 111, §3.2

import Mathlib
import Definitions.Def_HedgeInv_Order_Model

namespace HedgeInv.Order

/-- §3.2, p. 111: for an increasing, strictly concave, three times continuously differentiable
utility `u : ℝ → ℝ` with constant or decreasing absolute prudence `−u‴/u″`, the third derivative
`u‴` is nonincreasing. -/
theorem dap_third_deriv_antitone (u : ℝ → ℝ) (hu : ContDiff ℝ 3 u)
    (hu1 : ∀ w, 0 < deriv u w) (hu2 : ∀ w, deriv (deriv u) w < 0)
    (hDAP : Antitone (absPrudence u)) :
    Antitone (deriv (deriv (deriv u))) := by sorry

end HedgeInv.Order
