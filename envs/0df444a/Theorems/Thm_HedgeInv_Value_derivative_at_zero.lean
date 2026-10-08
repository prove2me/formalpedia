-- Prove2me | Theorems.Thm_HedgeInv_Value_derivative_at_zero
-- name    : HedgeInv.Value.derivative_at_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:18:43.207322+00:00
-- url     : https://prove2.me/theorems/7daaf467-643d-40a1-8681-c7c041ff6777
-- title:
--   Proof of Proposition 5, p. 118 — the derivative of $\mathbb E[u(\Pi_H(I,\alpha))]$ at $\alpha=0$ is $\mathbb E[u'(W+\Pi_U(I))\{-X_T+X_0e^{rT}\}]$
-- statement:
--   Consider the hedged newsvendor of Gaur and Seshadri in scaled units: scaled wealth $W$, demand parameters $a$ and $b>0$, an order quantity $I>\max\{a,0\}$, and a scaled unit cost $c_1$ with $0<c_1$ and $c_1b<1$ (the scaled form of $p>ce^{rT}>s$). The asset price $S_T$ has law $\nu$ and the scaled forecast error $\varepsilon$ has law $G$, both probability measures on $\mathbb R$, with $\mathbb E[\varepsilon]=0$ and $\mathbb E[\varepsilon^2]<\infty$; $S_T$ and $\varepsilon$ are independent. The hedge pays $X_T=\varphi(S_T)$ for a nondecreasing, measurable, $\nu$-integrable $\varphi$, and its forward price $X_0e^{rT}$ satisfies the fair-gamble condition (12), $\mathbb E[X_T]=X_0e^{rT}$. Let $u$ be a concave, differentiable utility function on $\mathbb R$.
--
--   Suppose that for some $\delta>0$ the utility $u(\Pi_H(I,\alpha))$ of the hedged wealth is integrable at $\alpha=-\delta$, $\alpha=0$ and $\alpha=\delta$. Then $\alpha\mapsto\mathbb E[u(\Pi_H(I,\alpha))]$ is differentiable at $\alpha=0$, and
--   $$\frac{d}{d\alpha}\mathbb E[u(\Pi_H(I,\alpha))]\Big|_{\alpha=0} = \mathbb E\Big[u'\big(W+\min\{S_T+\varepsilon,(I-a)/b\}-c_1I\big)\,\{-X_T+X_0e^{rT}\}\Big].$$
--
--   This is the first step of the authors' proof of Proposition 5: it identifies the marginal value of a small short position in the hedge with an expectation that the second step shows to be nonnegative.
--
--   **Formalization Note** The derivative is two-sided ($\alpha<0$ means buying the portfolio). The paper differentiates under the expectation without comment; the integrability at $\alpha\in\{-\delta,0,\delta\}$ is the regularity assumption that makes this legitimate, and is added. The standing assumptions of §2–§3 ($b>0$, $I>\max\{a,0\}$, $p>ce^{rT}>s$, $\mathbb E[\varepsilon]=0$, $\mathbb E[\varepsilon^2]<\infty$, (12), $X_T$ increasing in $S_T$) are carried although this step does not use all of them.
-- source:
--   Gaur & Seshadri, Hedging Inventory Risk Through Market Instruments, Manuf. Serv. Oper. Manag. 7(2) (2005), p. 118, Appendix, proof of Proposition 5, first sentence and display; setting (11), (12), (14) on pp. 110–111

import Mathlib
import Definitions.Def_HedgeInv_Value_Model
open MeasureTheory

namespace HedgeInv.Value

/-- Proof of Proposition 5, p. 118 (Gaur & Seshadri 2005): the first derivative of the expected
utility (14) in the hedge ratio `α`, evaluated at `α = 0`, is
`E[u′(W + min{S_T + ε, (I − a)/b} − c₁I){−X_T + X₀e^{rT}}]`. The derivative is two-sided. -/
theorem derivative_at_zero
    (ν G : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure G]
    (hG_mean : ∫ e, e ∂G = 0) (hG_L2 : MemLp id 2 G)
    (W a b c₁ I : ℝ) (hb : 0 < b) (hI : max a 0 < I) (hc₁ : 0 < c₁) (hc₁b : c₁ * b < 1)
    (φ : ℝ → ℝ) (hφ_mono : Monotone φ) (hφ_meas : Measurable φ) (hφ_int : Integrable φ ν)
    (x0r : ℝ) (h12 : ∫ s, φ s ∂ν = x0r)
    (u : ℝ → ℝ) (hu_conc : ConcaveOn ℝ Set.univ u) (hu_diff : Differentiable ℝ u)
    (δ : ℝ) (hδ : 0 < δ)
    (hint : ∀ α ∈ ({-δ, 0, δ} : Set ℝ),
      Integrable (fun p : ℝ × ℝ => u (HedgeInv.Order.hedgedPayoff W a b c₁ φ x0r I α p.1 p.2)) (ν.prod G)) :
    HasDerivAt (fun α => HedgeInv.Order.expUtil ν G u W a b c₁ φ x0r I α)
      (∫ p : ℝ × ℝ, deriv u (unhedgedPayoff W a b c₁ I p.1 p.2) * (x0r - φ p.1) ∂(ν.prod G)) 0 := by sorry

end HedgeInv.Value
