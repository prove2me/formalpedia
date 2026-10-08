-- Prove2me | Theorems.Thm_HedgeInv_Order_increasing_differences
-- name    : HedgeInv.Order.increasing_differences
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:39.453001+00:00
-- url     : https://prove2.me/theorems/9dec7b54-0e21-468a-ab86-a97f6467337c
-- title:
--   Proof of Proposition 7, p. 118 — ∂²E[u(Π)]/∂I∂α ≥ 0: E[u(Π_H(I, α))] has increasing differences in (I, α)
-- statement:
--   Work in the hedged newsvendor model under its standing assumptions, with a utility $u$ in the class of Proposition 7, the $\bar\alpha$-condition and the regularity condition. Let $\max\{a,0\}<I\le I'$ and $0\le\alpha\le\alpha'\le\bar\alpha$. Then
--   $$E[u(\Pi_H(I',\alpha))]-E[u(\Pi_H(I,\alpha))]\ \le\ E[u(\Pi_H(I',\alpha'))]-E[u(\Pi_H(I,\alpha'))].$$
--
--   The marginal value of extra inventory is nondecreasing in the hedge ratio. This is what turns into monotonicity of the optimal order quantity.
--
--   **Formalization Note.** The paper claims $\partial^2E[u(\Pi)]/\partial I\partial\alpha\ge0$. It is stated here in integrated form (increasing differences on $(\max\{a,0\},\infty)\times[0,\bar\alpha]$), which needs no differentiability of the expectation. For a twice continuously differentiable expectation the two forms are equivalent.
-- source:
--   Gaur & Seshadri, Hedging Inventory Risk Through Market Instruments, Manuf. Serv. Oper. Manag. 7(2) (2005), pp. 118–119, Appendix, proof of Proposition 7, displays (24)–(26)

import Mathlib
import Definitions.Def_HedgeInv_Order_Model

namespace HedgeInv.Order

open MeasureTheory

/-- Proof of Proposition 7, pp. 118–119, the claim `∂²E[u(Π)]/∂I∂α ≥ 0` in integrated form:
`E[u(Π_H(I, α))]` has increasing differences in `(I, α)` on `(max{a, 0}, ∞) × [0, ᾱ]`. -/
theorem increasing_differences (ν G : Measure ℝ) (u : ℝ → ℝ) (W a b c₁ : ℝ) (φ : ℝ → ℝ)
    (x0r αbar : ℝ)
    (hstd : StandingAssumptions ν G b c₁ φ x0r) (hu : IsDARADAPUtility u)
    (hαbar : AlphaBarCond G W a b c₁ φ x0r αbar)
    (hreg : RegularityCond ν G u W a b c₁ φ x0r αbar)
    (I I' α α' : ℝ) (hI : max a 0 < I) (hII' : I ≤ I')
    (hα : 0 ≤ α) (hαα' : α ≤ α') (hα' : α' ≤ αbar) :
    expUtil ν G u W a b c₁ φ x0r I' α - expUtil ν G u W a b c₁ φ x0r I α ≤
      expUtil ν G u W a b c₁ φ x0r I' α' - expUtil ν G u W a b c₁ φ x0r I α' := by sorry

end HedgeInv.Order
