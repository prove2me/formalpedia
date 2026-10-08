-- Prove2me | Theorems.Thm_HedgeInv_Order_proposition7_order_monotone
-- name    : HedgeInv.Order.proposition7_order_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:51.196581+00:00
-- url     : https://prove2.me/theorems/561e7ef3-9f29-4138-ba17-d06546660bb4
-- title:
--   Proposition 7, p. 112 — with DARA and DAP utility and 0 ≤ α ≤ ᾱ, the optimal order I*(α) is nondecreasing in the hedge ratio α
-- statement:
--   Consider a newsvendor who stocks $I$ units, with demand $a+b(S_T+\varepsilon)$, and who shorts $\alpha$ units of a fair hedging portfolio $X_T=\varphi(S_T)$ that is increasing in the asset price $S_T$. The scaled terminal wealth is
--   $$\Pi_H(I,\alpha)=W+\min\Big\{S_T+\varepsilon,\frac{I-a}{b}\Big\}-c_1I-\alpha X_T+\alpha X_0e^{rT}.$$
--   Make the standing assumptions of the model (`HedgeInv.Order.Model`): $S_T$ and $\varepsilon$ independent, $E[\varepsilon]=0$, $E[\varepsilon^2]<\infty$, $b>0$, $0<c_1<1/b$, $X_T$ nondecreasing in $S_T$ and integrable, and $E[X_T]=X_0e^{rT}$.
--
--   Let $u$ be an increasing, concave, differentiable utility with constant or decreasing absolute risk aversion and constant or decreasing absolute prudence. Let $\bar\alpha\ge0$ satisfy the $\bar\alpha$-condition: $E_\varepsilon[\Pi_H(I,\alpha)\mid S_T]$ is nondecreasing in $S_T$ for every $\alpha\in[0,\bar\alpha]$ and every $I>\max\{a,0\}$. Assume the regularity condition of the model. For each $\alpha\in[0,\bar\alpha]$, let $I^*(\alpha)>\max\{a,0\}$ maximize $I\mapsto E[u(\Pi_H(I,\alpha))]$ over $I>\max\{a,0\}$. Then
--   $$\alpha\ \longmapsto\ I^*(\alpha)\quad\text{is nondecreasing on } [0,\bar\alpha].$$
--
--   Financial hedging raises the risk-averse newsvendor's optimal stocking level and moves it towards the risk-neutral quantity.
--
--   **Formalization Note.**
--   1. The paper's conclusion $dI^*/d\alpha\ge0$ is stated as monotonicity of $I^*$ on $[0,\bar\alpha]$, which needs no differentiability of $I^*$. The maximizer is unique because the objective is strictly concave in $I$, so any selection $I^*$ may be used.
--   2. "Concave, differentiable" is taken as $C^3$ with $u''<0$ everywhere, since absolute prudence $-u'''/u''$ must be defined.
--   3. $\bar\alpha$ is any value satisfying the $\bar\alpha$-condition. This includes the paper's largest such value, so the result is no weaker.
--   4. The integrability hypotheses record the differentiation under the expectation that the proof uses without comment.
-- source:
--   Gaur & Seshadri, Hedging Inventory Risk Through Market Instruments, Manuf. Serv. Oper. Manag. 7(2) (2005), p. 112, Proposition 7; proof pp. 118–119

import Mathlib
import Definitions.Def_HedgeInv_Order_Model

namespace HedgeInv.Order

open MeasureTheory

/-- Proposition 7, p. 112: for an increasing, concave, differentiable utility with constant or
decreasing absolute risk aversion and constant or decreasing absolute prudence, the optimal
inventory level `I*(α)` is nondecreasing in the hedge ratio `α` on `[0, ᾱ]`. -/
theorem proposition7_order_monotone (ν G : Measure ℝ) (u : ℝ → ℝ) (W a b c₁ : ℝ)
    (φ : ℝ → ℝ) (x0r αbar : ℝ)
    (hstd : StandingAssumptions ν G b c₁ φ x0r) (hu : IsDARADAPUtility u)
    (hαbar : AlphaBarCond G W a b c₁ φ x0r αbar)
    (hreg : RegularityCond ν G u W a b c₁ φ x0r αbar)
    (Istar : ℝ → ℝ)
    (hIdom : ∀ α ∈ Set.Icc (0 : ℝ) αbar, max a 0 < Istar α)
    (hmax : ∀ α ∈ Set.Icc (0 : ℝ) αbar,
      IsMaxOn (fun I => expUtil ν G u W a b c₁ φ x0r I α) (Set.Ioi (max a 0)) (Istar α)) :
    MonotoneOn Istar (Set.Icc (0 : ℝ) αbar) := by sorry

end HedgeInv.Order
