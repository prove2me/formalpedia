-- Prove2me | Theorems.Thm_NecoaraNG_FGM_lemma_1
-- name    : NecoaraNG.FGM.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:39.726975+00:00
-- url     : https://prove2.me/theorems/c2006897-cf6b-484f-bfa0-e6524d111504
-- title:
--   Lemma 1, p. 24 — φ_k(y*) ≤ (1 − λ_k) f* + λ_k φ₀(y*) when all y^k project to y*
-- statement:
--   Let $X$, $f$, $L_f$, $\kappa$ be as in problem (P), with $f$ convex, differentiable and $L_f$-smooth on $\mathbb{R}^n$ and quasi-strongly convex with constant $\kappa > 0$ at every point of $\mathbb{R}^n$. Let $(y^k)_{k \ge 0}$ be an arbitrary sequence whose nearest points in $X^*$ all equal one point $y^*$: $[y^k]_{X^*} = y^*$ for all $k \ge 0$. Let $x^0 = y^0$ and $x^{k+1} = [y^k - \frac{1}{L_f}\nabla f(y^k)]_X$, and let $\alpha_k \in (0, 1)$ for all $k$. With $\lambda_k$ and $\phi_k$ defined by $\lambda_0 = 1$, $\lambda_{k+1} = (1-\alpha_k)\lambda_k$, $\phi_0(z) = f(y^0) + \frac{\kappa}{2}\|z - y^0\|^2$ and the recursion (55), we have
--   $$\phi_k(y^*) \le (1 - \lambda_k) f^* + \lambda_k \phi_0(y^*) \qquad \text{for all } k \ge 0 .$$
--
--   This is the estimate-sequence property (56) that turns the lower models (54) into a rate.
--
--   **Formalization Note** $f^*$ is $f(x^*)$ for a fixed minimizer $x^* \in X^*$. Smoothness, convexity and (10) are assumed on $\mathbb{R}^n$ because (54) is applied at the points $y^k$, which may lie outside $X$.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 24, Lemma 1, (55)–(56)

import Mathlib
import Definitions.Def_NecoaraNG_FGM_Setting

namespace NecoaraNG.FGM

open scoped InnerProductSpace

/-- Lemma 1, p. 24: for any sequence `y^k` whose nearest points in `X*` all equal `y*`,
`x⁰ = y⁰`, `x^{k+1} = [y^k - (1/L_f)∇f(y^k)]_X` and `α_k ∈ (0, 1)`, the estimate functions (55)
satisfy `φ_k(y*) ≤ (1 - λ_k) f* + λ_k φ₀(y*)` for all `k ≥ 0` (56). -/
theorem lemma_1 {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hdiff : ∀ x, DifferentiableAt ℝ f x) (hf : ConvexOn ℝ Set.univ f)
    (Lf : ℝ) (hLf : 0 < Lf) (hL : ∀ x y, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (κ : ℝ) (hκ : 0 < κ) (hqs : QuasiStrongEverywhere X f κ)
    (y : ℕ → NecoaraNG.Chain.E n) (ystar : NecoaraNG.Chain.E n) (hsame : ∀ k, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) (y k) ystar)
    (x : ℕ → NecoaraNG.Chain.E n) (hx0 : x 0 = y 0)
    (hx : ∀ k, NecoaraNG.Chain.IsNearest X (y k - (1 / Lf) • gradient f (y k)) (x (k + 1)))
    (α : ℕ → ℝ) (hα : ∀ k, 0 < α k ∧ α k < 1) :
    ∀ k : ℕ, phi f Lf κ α x y k ystar ≤
      (1 - lam α k) * f xstar + lam α k * phi f Lf κ α x y 0 ystar := by sorry

end NecoaraNG.FGM
