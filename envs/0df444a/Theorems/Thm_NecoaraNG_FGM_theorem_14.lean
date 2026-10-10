-- Prove2me | Theorems.Thm_NecoaraNG_FGM_theorem_14
-- name    : NecoaraNG.FGM.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:30.275055+00:00
-- url     : https://prove2.me/theorems/c1dbe41d-b733-410e-9558-bb6b2567ed9b
-- title:
--   Theorem 14, p. 25 — (FGM) on qS_{L_f,κ_f}: f(x^k) − f* ≤ (1 − √μ_f)^k · 2(f(x⁰) − f*) if all y^k share one projection
-- statement:
--   Let $X \subseteq \mathbb{R}^n$ be closed and convex, and let $f : \mathbb{R}^n \to \mathbb{R}$ be convex and differentiable with $L_f$-Lipschitz gradient ($L_f > 0$). Assume problem (P), $\min_{x \in X} f(x)$, has a minimizer $x^*$, write $f^* = f(x^*)$ and $X^*$ for the optimal set, and assume $f$ is quasi-strongly convex with constant $\kappa > 0$: for every $x$ and every nearest point $\bar x = [x]_{X^*}$,
--   $f^* \ge f(x) + \langle \nabla f(x), \bar x - x\rangle + \frac{\kappa}{2}\|x - \bar x\|^2$.
--
--   Run the fast gradient method (FGM) from $x^0 = y^0 \in X$:
--   $$x^{k+1} = \Big[y^k - \tfrac{1}{L_f}\nabla f(y^k)\Big]_X, \qquad y^{k+1} = x^{k+1} + \beta\,(x^{k+1} - x^k), \qquad \beta = \frac{\sqrt{L_f} - \sqrt{\kappa}}{\sqrt{L_f} + \sqrt{\kappa}} .$$
--   If all iterates $y^k$ have the same nearest point $y^*$ in $X^*$, then, with $\mu_f = \kappa / L_f$,
--   $$f(x^k) - f^* \le \big(1 - \sqrt{\mu_f}\big)^k \cdot 2\big(f(x^0) - f^*\big) \qquad \text{for all } k \ge 0 .$$
--
--   This is the accelerated linear rate for quasi-strongly convex problems: the dependence on the condition number is $\sqrt{\mu_f}$ instead of the $\mu_f$ of the projected gradient method.
--
--   **Formalization Note** Quasi-strong convexity (10), smoothness and convexity are assumed on all of $\mathbb{R}^n$, not only on $X$, because the proof applies (54) and (29) at the extrapolated points $y^k$, which may lie outside $X$; for $X = \mathbb{R}^n$ (the case of Remark 1) these are exactly the paper's hypotheses. Projections are nearest-point predicates; iterates are 0-based (the page's "for $k \ge 1$" in (FGM) is a slip). No hypothesis $\kappa \le L_f$ is added: it follows from the hypotheses (descent inequality and (10) at any point outside $X^*$) unless $X^* = \mathbb{R}^n$, in which case $f$ is constant and the bound is trivial.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 25, Theorem 14, (60)

import Mathlib
import Definitions.Def_NecoaraNG_FGM_Setting

namespace NecoaraNG.FGM

open scoped InnerProductSpace

/-- Theorem 14, p. 25: (FGM) with constant parameter `β = (√L_f - √κ)/(√L_f + √κ)` on
`f ∈ qS_{L_f,κ}` (smoothness, convexity and (10) on all of `ℝⁿ`), provided all iterates `y^k`
have the same nearest point `y*` in `X*`, satisfies
`f(x^k) - f* ≤ (1 - √μ_f)^k · 2 (f(x⁰) - f*)` with `μ_f = κ/L_f` (60). -/
theorem theorem_14 {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hdiff : ∀ x, DifferentiableAt ℝ f x) (hf : ConvexOn ℝ Set.univ f)
    (Lf : ℝ) (hLf : 0 < Lf) (hL : ∀ x y, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (κ : ℝ) (hκ : 0 < κ) (hqs : QuasiStrongEverywhere X f κ)
    (x y : ℕ → NecoaraNG.Chain.E n)
    (hrun : IsFGMRun X f Lf ((Real.sqrt Lf - Real.sqrt κ) / (Real.sqrt Lf + Real.sqrt κ)) x y)
    (ystar : NecoaraNG.Chain.E n) (hsame : ∀ k, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) (y k) ystar) :
    ∀ k : ℕ, f (x k) - f xstar ≤ (1 - Real.sqrt (κ / Lf)) ^ k * (2 * (f (x 0) - f xstar)) := by sorry

end NecoaraNG.FGM
