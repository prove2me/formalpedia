-- Prove2me | Theorems.Thm_OnlineConvexOpt_ConvexBasics_strong_convexity_smoothness_gap_bounds
-- name    : OnlineConvexOpt.ConvexBasics.strong_convexity_smoothness_gap_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T18:34:38.637296+00:00
-- url     : https://prove2.me/theorems/a4c47add-043e-414f-9756-1a18a367dfdd
-- title:
--   Lemma 2.4 — potential-function bounds on the optimality gap
-- statement:
--   **Statement (Lemma 2.4).** Let $f : E \to \mathbb{R}$ have global gradient map $g$ and let $x^\star$ minimize $f$ over all of $E$. Write $h_x := f(x) - f(x^\star)$ for the distance to optimality in value, $d_x := \|x - x^\star\|$ for the Euclidean distance to the minimizer, and $\nabla_x := g(x)$ for the gradient at $x$. If $f$ is $\alpha$-strongly convex and $\beta$-smooth (both over all of $E$), then for every point $x$:
--   $$\frac{\alpha}{2} d_x^2 \le h_x, \qquad h_x \le \frac{\beta}{2} d_x^2, \qquad \frac{1}{2\beta}\|\nabla_x\|^2 \le h_x, \qquad h_x \le \frac{1}{2\alpha}\|\nabla_x\|^2.$$
--
--   These four inequalities are the potential-function relations the chapter uses throughout to move between three different measures of progress — function-value gap, distance to the minimizer, and gradient norm — substituting one for another as each convergence proof needs. The first two follow directly from strong convexity and smoothness applied at $(x, x^\star)$ together with $\nabla f(x^\star) = 0$; the third is proved via one step of gradient descent with step size $1/\beta$ from $x$; the fourth by minimizing the strong-convexity lower bound over all $z \in E$.
--
--   **Formalization Note.** The lemma is stated for a single point $x$ (matching its use throughout the chapter at each iterate $x_t$ of a sequence) rather than for a whole trajectory. All four properties are proved under the conjunction of strong convexity and smoothness, since that is the standing hypothesis of the sections that invoke this lemma; the book's own proof in fact only uses strong convexity for the first and fourth bounds and smoothness for the second and third, but the mission does not split the statement into two separate lemmas since the book itself states and proves all four together under both hypotheses.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, pp. 24-25, Lemma 2.4 (PDF pp. 46-47)

import Mathlib
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn
import Definitions.Def_OnlineConvexOpt_ConvexBasics_SmoothOn

namespace OnlineConvexOpt.ConvexBasics

/-- Lemma 2.4 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, pp. 24-25, PDF pp. 46-47). Let `f : R^d → R` be `α`-strongly convex and/or
`β`-smooth with global gradient map `g` and minimizer `x⋆`. Writing `h_t := f(x_t) - f(x⋆)`,
`d_t := ‖x_t - x⋆‖` and `∇_t := g(x_t)` for any point `x_t`, the following properties hold:
1. `(α/2) d_t² ≤ h_t`
2. `h_t ≤ (β/2) d_t²`
3. `(1/(2β)) ‖∇_t‖² ≤ h_t`
4. `h_t ≤ (1/(2α)) ‖∇_t‖²` -/
theorem strong_convexity_smoothness_gap_bounds {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ) (g : E → E)
    (hgrad : ∀ z, HasGradientAt f (g z) z)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (xstar : E) (hxstar : IsMinOn f Set.univ xstar)
    (hsc : StronglyConvexOn Set.univ f g α) (hsm : SmoothOn Set.univ f g β)
    (x : E) :
    (α / 2) * ‖x - xstar‖ ^ 2 ≤ f x - f xstar ∧
      f x - f xstar ≤ (β / 2) * ‖x - xstar‖ ^ 2 ∧
      (1 / (2 * β)) * ‖g x‖ ^ 2 ≤ f x - f xstar ∧
      f x - f xstar ≤ (1 / (2 * α)) * ‖g x‖ ^ 2 := by sorry

end OnlineConvexOpt.ConvexBasics
