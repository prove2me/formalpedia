-- Prove2me | Theorems.Thm_HedgeInv_Value_covariance_inequality
-- name    : HedgeInv.Value.covariance_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:19:04.119675+00:00
-- url     : https://prove2.me/theorems/47417f87-4906-4ed7-a27c-8fbdb510a5f8
-- title:
--   Proof of Proposition 5, p. 118 — $\mathbb E[u'(W+\Pi_U)\{-X_T+X_0e^{rT}\}] \ge \mathbb E[u'(W+\Pi_U)]\cdot\mathbb E[-X_T+X_0e^{rT}] = 0$
-- statement:
--   Work in the setting of the hedged newsvendor of Gaur and Seshadri, in scaled units: scaled wealth $W$, demand parameters $a$ and $b>0$, order quantity $I>\max\{a,0\}$, scaled unit cost $c_1$ with $0<c_1$ and $c_1b<1$; independent $S_T\sim\nu$ and $\varepsilon\sim G$ (probability measures on $\mathbb R$) with $\mathbb E[\varepsilon]=0$, $\mathbb E[\varepsilon^2]<\infty$; a hedge $X_T=\varphi(S_T)$ with $\varphi$ nondecreasing, measurable and $\nu$-integrable, whose forward price $X_0e^{rT}$ satisfies (12), $\mathbb E[X_T - X_0e^{rT}] = 0$. Let $u$ be concave and differentiable on $\mathbb R$, and write
--   $$W+\Pi_U = W+\min\{S_T+\varepsilon,(I-a)/b\}-c_1I$$
--   for the unhedged wealth.
--
--   Suppose $u'(W+\Pi_U)$ and $u'(W+\Pi_U)\{-X_T+X_0e^{rT}\}$ are integrable. Since $u'(W+\Pi_U)$ is a decreasing function of $S_T$ and so is $-X_T+X_0e^{rT}$, they have a nonnegative covariance:
--   $$\mathbb E\big[u'(W+\Pi_U)\{-X_T+X_0e^{rT}\}\big] \;\ge\; \mathbb E\big[u'(W+\Pi_U)\big]\cdot\mathbb E\big[-X_T+X_0e^{rT}\big],$$
--   and the last factor is $\mathbb E[-X_T+X_0e^{rT}]=0$ by (12).
--
--   This is the second step of the proof of Proposition 5: together with the derivative formula it shows that the marginal value of a small fair hedge is nonnegative.
--
--   **Formalization Note** All expectations are taken over the product law $\nu\otimes G$ of $(S_T,\varepsilon)$. "Positive covariance" in the paper is read as nonnegative covariance, which is what the printed $\ge$ requires. No sign of $u'$ is assumed (the inequality holds for any concave $u$). The integrability of $u'(W+\Pi_U)$ is added because the paper writes its expectation as a factor.
-- source:
--   Gaur & Seshadri, Hedging Inventory Risk Through Market Instruments, Manuf. Serv. Oper. Manag. 7(2) (2005), p. 118, Appendix, proof of Proposition 5, second sentence and the display after it; (12) on p. 111

import Mathlib
import Definitions.Def_HedgeInv_Value_Model
open MeasureTheory

namespace HedgeInv.Value

/-- Proof of Proposition 5, p. 118 (Gaur & Seshadri 2005): `u′(Π_U)` and `−X_T + X₀e^{rT}` are both
decreasing in `S_T`, so they have a nonnegative covariance,
`E[u′(Π_U){−X_T + X₀e^{rT}}] ≥ E[u′(Π_U)] · E[−X_T + X₀e^{rT}]`, and the last factor is `0` by (12). -/
theorem covariance_inequality
    (ν G : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure G]
    (hG_mean : ∫ e, e ∂G = 0) (hG_L2 : MemLp id 2 G)
    (W a b c₁ I : ℝ) (hb : 0 < b) (hI : max a 0 < I) (hc₁ : 0 < c₁) (hc₁b : c₁ * b < 1)
    (φ : ℝ → ℝ) (hφ_mono : Monotone φ) (hφ_meas : Measurable φ) (hφ_int : Integrable φ ν)
    (x0r : ℝ) (h12 : ∫ s, φ s ∂ν = x0r)
    (u : ℝ → ℝ) (hu_conc : ConcaveOn ℝ Set.univ u) (hu_diff : Differentiable ℝ u)
    (hint_du : Integrable (fun p : ℝ × ℝ => deriv u (unhedgedPayoff W a b c₁ I p.1 p.2)) (ν.prod G))
    (hint_prod : Integrable
      (fun p : ℝ × ℝ => deriv u (unhedgedPayoff W a b c₁ I p.1 p.2) * (x0r - φ p.1)) (ν.prod G)) :
    (∫ p : ℝ × ℝ, deriv u (unhedgedPayoff W a b c₁ I p.1 p.2) ∂(ν.prod G)) *
        (∫ p : ℝ × ℝ, (x0r - φ p.1) ∂(ν.prod G)) ≤
      ∫ p : ℝ × ℝ, deriv u (unhedgedPayoff W a b c₁ I p.1 p.2) * (x0r - φ p.1) ∂(ν.prod G) ∧
    ∫ p : ℝ × ℝ, (x0r - φ p.1) ∂(ν.prod G) = 0 := by sorry

end HedgeInv.Value
