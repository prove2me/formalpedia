-- Prove2me | Theorems.Thm_NecoaraNG_FGM_ineq_54
-- name    : NecoaraNG.FGM.ineq_54
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:46:43.080715+00:00
-- url     : https://prove2.me/theorems/cddef2c7-c390-409f-9e2a-a27e4eeb2e7a
-- title:
--   (54), p. 24 — f* ≥ f(x⁺) + ⟨g(x), x̄ − x⟩ + ‖g(x)‖²/(2L_f) + κ_f/2 ‖x̄ − x‖² for all x ∈ ℝⁿ
-- statement:
--   Let $X \subseteq \mathbb{R}^n$ be closed and convex, and let $f : \mathbb{R}^n \to \mathbb{R}$ be convex and differentiable on $\mathbb{R}^n$ with $L_f$-Lipschitz gradient ($L_f > 0$). Assume $X^*$ is nonempty and $f$ is quasi-strongly convex with constant $\kappa > 0$ at every point of $\mathbb{R}^n$. For $x \in \mathbb{R}^n$ let $x^+ = [x - \frac{1}{L_f}\nabla f(x)]_X$ be the projected gradient step and $g(x) = L_f(x - x^+)$ the gradient mapping. Then for every $x \in \mathbb{R}^n$, every nearest point $\bar x = [x]_{X^*}$ and every projected step $x^+$,
--   $$f^* \ge f(x^+) + \langle g(x), \bar x - x\rangle + \frac{1}{2L_f}\|g(x)\|^2 + \frac{\kappa}{2}\|\bar x - x\|^2 .$$
--
--   This is the inequality on which the estimate-sequence analysis of the fast gradient method rests: it plays the role of the strong-convexity lower model at the point $\bar x$.
--
--   **Formalization Note** The paper prints the last term as $\frac{\kappa_f}{2}\|\bar x - x\|$ without the square; the square is what (10) yields and what (55) uses, so it is stated with the square. $f^* = f(\bar x)$. Smoothness, convexity and (10) are assumed on $\mathbb{R}^n$ because the paper claims (54) "for all $x \in \mathbb{R}^n$" and applies it at extrapolated points outside $X$.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 24, display (54)

import Mathlib
import Definitions.Def_NecoaraNG_FGM_Setting

namespace NecoaraNG.FGM

open scoped InnerProductSpace

/-- (54), p. 24: for `f ∈ qS_{L_f,κ}` (with smoothness, convexity and (10) on all of `ℝⁿ`),
the gradient mapping `g(z) = L_f (z - z⁺)`, `z⁺ = [z - (1/L_f)∇f(z)]_X`, satisfies, for every
`z ∈ ℝⁿ` and `z̄ = [z]_{X*}`,
`f* ≥ f(z⁺) + ⟪g(z), z̄ - z⟫ + 1/(2L_f) ‖g(z)‖² + κ/2 ‖z̄ - z‖²` (the page omits the square). -/
theorem ineq_54 {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hdiff : ∀ x, DifferentiableAt ℝ f x) (hf : ConvexOn ℝ Set.univ f)
    (Lf : ℝ) (hLf : 0 < Lf) (hL : ∀ x y, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (κ : ℝ) (hκ : 0 < κ) (hqs : QuasiStrongEverywhere X f κ) :
    ∀ z zbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) z zbar →
      ∀ zp, NecoaraNG.Chain.IsNearest X (z - (1 / Lf) • gradient f z) zp →
        f zp + ⟪Lf • (z - zp), zbar - z⟫_ℝ + 1 / (2 * Lf) * ‖Lf • (z - zp)‖ ^ 2 +
          κ / 2 * ‖zbar - z‖ ^ 2 ≤ f zbar := by sorry

end NecoaraNG.FGM
