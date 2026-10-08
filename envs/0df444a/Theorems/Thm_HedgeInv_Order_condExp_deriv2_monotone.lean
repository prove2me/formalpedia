-- Prove2me | Theorems.Thm_HedgeInv_Order_condExp_deriv2_monotone
-- name    : HedgeInv.Order.condExp_deriv2_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:27.886578+00:00
-- url     : https://prove2.me/theorems/0f48a931-080e-4c5b-a9d4-bbe33eddba53
-- title:
--   Proof of Proposition 7, p. 119 — E_ε[u″(Π) | S_T] is increasing in S_T for 0 ≤ α ≤ ᾱ
-- statement:
--   Work in the hedged newsvendor model (`HedgeInv.Order.Model`) under its standing assumptions. Let $u$ be a utility in the class of Proposition 7: $C^3$, $u'>0$, $u''<0$, with nonincreasing absolute risk aversion and nonincreasing absolute prudence. Suppose the $\bar\alpha$-condition holds. Fix an inventory level $I>\max\{a,0\}$ and a hedge ratio $\alpha\in[0,\bar\alpha]$. Assume $\varepsilon\mapsto u''(\Pi_H(I,\alpha))$ is $G$-integrable at every $S_T=s$. Then
--   $$s\ \longmapsto\ E_\varepsilon\big[u''(\Pi_H(I,\alpha))\,\big|\,S_T=s\big]=\int u''\big(\Pi_H(I,\alpha)(s,e)\big)\,dG(e)$$
--   is nondecreasing in $s$.
--
--   In the proof of Proposition 7 this makes $-c_1E_\varepsilon[u''(\Pi)\mid S_T]$ a nonnegative, nonincreasing weight, so Lemma 2(i) applies to the first term of (25).
-- source:
--   Gaur & Seshadri, Hedging Inventory Risk Through Market Instruments, Manuf. Serv. Oper. Manag. 7(2) (2005), p. 119, Appendix, proof of Proposition 7

import Mathlib
import Definitions.Def_HedgeInv_Order_Model

namespace HedgeInv.Order

open MeasureTheory

/-- Proof of Proposition 7, p. 119: under the standing assumptions, for a DARA/CARA and DAP
utility, a hedge ratio `α ∈ [0, ᾱ]` and an inventory level `I > max{a, 0}`,
`s ↦ E_ε[u″(Π_H(I, α)) | S_T = s]` is nondecreasing. -/
theorem condExp_deriv2_monotone (ν G : Measure ℝ) (u : ℝ → ℝ) (W a b c₁ : ℝ) (φ : ℝ → ℝ)
    (x0r αbar I α : ℝ)
    (hstd : StandingAssumptions ν G b c₁ φ x0r) (hu : IsDARADAPUtility u)
    (hαbar : AlphaBarCond G W a b c₁ φ x0r αbar)
    (hI : max a 0 < I) (hα : α ∈ Set.Icc (0 : ℝ) αbar)
    (hint : ∀ s, Integrable (fun e => deriv (deriv u) (hedgedPayoff W a b c₁ φ x0r I α s e)) G) :
    Monotone (fun s => ∫ e, deriv (deriv u) (hedgedPayoff W a b c₁ φ x0r I α s e) ∂G) := by sorry

end HedgeInv.Order
