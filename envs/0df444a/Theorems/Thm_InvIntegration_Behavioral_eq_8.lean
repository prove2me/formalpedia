-- Prove2me | Theorems.Thm_InvIntegration_Behavioral_eq_8
-- name    : InvIntegration.Behavioral.eq_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:03.197402+00:00
-- url     : https://prove2.me/theorems/cb4130e9-d2be-4e82-87e5-f0b67637261a
-- title:
--   Eq. (8), p. 13 (PDF 13) — at equilibrium v∗ = (p − ξs)/(1 − ξδ) (when ξ ≥ 0)
-- statement:
--   Let $(q,v,\xi)$ be an equilibrium of a market $N(m,\mathrm{sd}^2)$ with $m>0$, $\mathrm{sd}>0$. Then $\xi\delta<1$,
--   $$v = \max\Bigl(\frac{p-\xi s}{1-\xi\delta},\ p\Bigr),$$
--   and, if $\xi\ge 0$,
--   $$v = \frac{p-\xi s}{1-\xi\delta}. \tag{8}$$
--
--   Equation (8) is the implicit equation for the equilibrium threshold valuation in terms of the equilibrium fill rate.
--
--   **Formalization Note.** With the paper's ratio fill rate (p. 13) and normal demand, the equilibrium fill rate can be negative, and then (8) fails while $v=p$; the guard $\xi\ge 0$ and the general form with the maximum are disclosed corrections.
-- source:
--   Aflaki & Swinney, Inventory Integration with Rational Consumers, SSRN preprint 2842182 (July 2020), p. 13 (PDF 13), eq. (8)

import Mathlib
import Definitions.Def_InvIntegration_Behavioral_Model

namespace InvIntegration.Behavioral

theorem eq_8 (P : Params) (hS : P.Standing) (m sd : ℝ) (hm : 0 < m) (hsd : 0 < sd)
    (q v ξ : ℝ) (hE : IsEquilibrium P m sd q v ξ) :
    ξ * P.δ < 1 ∧
    v = max ((P.p - ξ * P.s) / (1 - ξ * P.δ)) P.p ∧
    (0 ≤ ξ → v = (P.p - ξ * P.s) / (1 - ξ * P.δ)) := by sorry

end InvIntegration.Behavioral
