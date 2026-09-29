-- Prove2me | Theorems.Thm_OnlineConvexOpt_ConvexBasics_gradient_descent_polyak_convergence
-- name    : OnlineConvexOpt.ConvexBasics.gradient_descent_polyak_convergence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T18:35:15.767016+00:00
-- url     : https://prove2.me/theorems/38827468-ac63-4aad-806c-e1ff618fb5c0
-- title:
--   Theorem 2.3 — convergence of GD with the Polyak step size
-- statement:
--   **Statement (Theorem 2.3).** Let $f : E \to \mathbb{R}$ be convex with gradient map $g$ satisfying $\|g(z)\| \le G$ everywhere, and suppose $f$ is also $\alpha$-strongly convex and $\beta$-smooth (over all of $E$), with condition number $\gamma = \alpha/\beta$; let $x^\star$ minimize $f$. Run gradient descent with the Polyak step size (Algorithm 3) for $T \ge 1$ steps from $x_0$, and let $\bar{x}$ achieve $f(\bar{x}) = \min_{0 \le t \le T} f(x_t)$. Writing $d_0 := \|x_0 - x^\star\|$,
--   $$f(\bar{x}) - f(x^\star) \le B_T := \min\left\{ \frac{G d_0}{\sqrt{T}},\; \frac{2\beta d_0^2}{T},\; \frac{3G^2}{\alpha T},\; \beta d_0^2 \Big(1 - \frac{\gamma}{4}\Big)^T \right\}.$$
--
--   Each of the four terms in $B_T$ is the best available rate under a different subset of the hypotheses (general convex with bounded gradient; smooth; strongly convex; both), and the theorem's content is that the *same* algorithm — with no parameter tuning beyond the step size itself — automatically achieves whichever of the four rates applies, without needing to know in advance which properties $f$ has. The remarkable feature of the Polyak step size is that it requires none of $\alpha$, $\beta$, or $G$ to compute, only the (typically unknown, but here assumed available for the analysis) value $f(x^\star)$.
--
--   **Formalization Note.** $x$ is 0-indexed matching the book directly here (no round shift, since Algorithm 3 itself takes $x_0$ as input). $\bar{x}$ is characterized existentially as some $x_t$ with $t \le T$ minimizing $f(x_t)$ over that range, rather than by a `Finset.min'`/`argmin` idiom. All four explicit constants ($1$, $2$, $3$, $1/4$) are exactly the book's; none are rounded to a generic asymptotic rate.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 23, Theorem 2.3 (PDF pp. 45-46)

import Mathlib
import Definitions.Def_OnlineConvexOpt_ConvexBasics_GradientDescentPolyak
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn
import Definitions.Def_OnlineConvexOpt_ConvexBasics_SmoothOn

namespace OnlineConvexOpt.ConvexBasics

/-- Theorem 2.3 (GD with the Polyak step size; Hazan, *Introduction to Online Convex
Optimization*, 2nd ed., arXiv:1909.05207v3, p. 23, PDF p. 45). Let `f` be convex, `α`-strongly
convex and `β`-smooth with condition number `γ = α / β`, let `x⋆` minimize `f`, and assume the
gradient along the run's own iterates `x 0, ..., x T` is bounded by `G` (the book's "assume
`‖∇t‖ ≤ G`", p. 23: a bound on the realized gradients `∇_0, ..., ∇_{T-1}` of this specific run,
not a global Lipschitz bound on `f` — a global bound would be inconsistent with global strong
convexity on an infinite-dimensional/unbounded `E`, since a strongly convex function's gradient
necessarily grows without bound away from its minimizer). For a run `x` of Algorithm 3
(`IsGradientDescentPolyak`) and horizon `T ≥ 1`, if `x̄` achieves
`f(x̄) = min_{0 ≤ t ≤ T} f(x_t)` (the algorithm's return value), then
`f(x̄) - f(x⋆) ≤ B_T`, where, with `d₀ := ‖x_0 - x⋆‖`,
`B_T = min{ G d₀ / √T, 2β d₀² / T, 3G² / (αT), β d₀² (1 - γ/4)^T }`. -/
theorem gradient_descent_polyak_convergence {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ) (g : E → E) (α β G : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hG : 0 < G)
    (hfconv : ConvexOn ℝ Set.univ f)
    (hsc : StronglyConvexOn Set.univ f g α) (hsm : SmoothOn Set.univ f g β)
    (xstar : E) (hxstar : IsMinOn f Set.univ xstar)
    (x : ℕ → E) (hGD : IsGradientDescentPolyak f xstar g x)
    (T : ℕ) (hT : 0 < T)
    (hGbound : ∀ t ≤ T, ‖g (x t)‖ ≤ G)
    (xbar : E) (hxbar : ∃ t ≤ T, xbar = x t ∧ ∀ s ≤ T, f (x t) ≤ f (x s)) :
    f xbar - f xstar ≤
      min (G * ‖x 0 - xstar‖ / Real.sqrt T)
        (min (2 * β * ‖x 0 - xstar‖ ^ 2 / T)
          (min (3 * G ^ 2 / (α * T))
            (β * ‖x 0 - xstar‖ ^ 2 * (1 - α / β / 4) ^ T))) := by sorry

end OnlineConvexOpt.ConvexBasics
