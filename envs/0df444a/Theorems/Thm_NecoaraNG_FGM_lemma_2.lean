-- Prove2me | Theorems.Thm_NecoaraNG_FGM_lemma_2
-- name    : NecoaraNG.FGM.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:21.090295+00:00
-- url     : https://prove2.me/theorems/be3a6f37-eb99-4017-b841-8d2652a215fc
-- title:
--   Lemma 2, p. 25 — if f(x^k) ≤ min φ_k then f(x^k) − f* ≤ λ_k (f(x⁰) − f* + γ₀/2 ‖y* − y⁰‖²)
-- statement:
--   Under the assumptions of Lemma 1 (with $\gamma_0 = \kappa$), suppose in addition that
--   $$f(x^k) \le \phi_k^* = \min_{z \in \mathbb{R}^n} \phi_k(z) \qquad \text{for all } k \ge 0 . \tag{58}$$
--   Then
--   $$f(x^k) - f^* \le \lambda_k\Big(f(x^0) - f^* + \frac{\kappa}{2}\|y^* - y^0\|^2\Big) \qquad \text{for all } k \ge 0 .$$
--
--   Together with Lemma 1 this reduces the convergence of any scheme of this form to checking (58).
--
--   **Formalization Note** Condition (58) is written as $f(x^k) \le \phi_k(z)$ for every $z \in \mathbb{R}^n$, which is equivalent because the minimum of the strongly convex quadratic $\phi_k$ is attained. The paper prints $\frac{\gamma_0}{2}\|y^* - y^0\|$ without the square; the proof's last line is $\lambda_k(\phi_0(y^*) - f^*)$ with $\phi_0(y^*) = f(y^0) + \frac{\gamma_0}{2}\|y^* - y^0\|^2$, so the square is stated. Smoothness, convexity and (10) are assumed on $\mathbb{R}^n$, as in Lemma 1.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 25, Lemma 2, (58)–(59)

import Mathlib
import Definitions.Def_NecoaraNG_FGM_Setting

namespace NecoaraNG.FGM

open scoped InnerProductSpace

/-- Lemma 2, p. 25: under the assumptions of Lemma 1, if moreover `f(x^k) ≤ φ_k(z)` for every
`z ∈ ℝⁿ` and every `k` (i.e. `f(x^k) ≤ φ*_k = min φ_k`, (58)), then
`f(x^k) - f* ≤ λ_k (f(x⁰) - f* + κ/2 ‖y* - y⁰‖²)` (59; the page omits the square). -/
theorem lemma_2 {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hdiff : ∀ x, DifferentiableAt ℝ f x) (hf : ConvexOn ℝ Set.univ f)
    (Lf : ℝ) (hLf : 0 < Lf) (hL : ∀ x y, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (κ : ℝ) (hκ : 0 < κ) (hqs : QuasiStrongEverywhere X f κ)
    (y : ℕ → NecoaraNG.Chain.E n) (ystar : NecoaraNG.Chain.E n) (hsame : ∀ k, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) (y k) ystar)
    (x : ℕ → NecoaraNG.Chain.E n) (hx0 : x 0 = y 0)
    (hx : ∀ k, NecoaraNG.Chain.IsNearest X (y k - (1 / Lf) • gradient f (y k)) (x (k + 1)))
    (α : ℕ → ℝ) (hα : ∀ k, 0 < α k ∧ α k < 1)
    (hmin : ∀ k z, f (x k) ≤ phi f Lf κ α x y k z) :
    ∀ k : ℕ, f (x k) - f xstar ≤
      lam α k * (f (x 0) - f xstar + κ / 2 * ‖ystar - y 0‖ ^ 2) := by sorry

end NecoaraNG.FGM
