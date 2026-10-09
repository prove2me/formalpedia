-- Prove2me | Theorems.Thm_NesterovODE_StrongCvx_theorem_5
-- name    : NesterovODE.StrongCvx.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:37:23.474719+00:00
-- url     : https://prove2.me/theorems/8b2259dd-33a6-4eea-ae06-fc87c7f085fa
-- title:
--   Theorem 5, p. 13 — inverse-square and integral error bounds
-- statement:
--   Let $r>3$, $f\in\mathcal F_L$, and let $x^\star$ minimize $f$. A solution $(X,V)$ of (17) satisfies, for every $t>0$,
--
--   $$f(X(t))-f^\star\leq\frac{(r-1)^2\|x_0-x^\star\|^2}{2t^2},\qquad \int_0^\infty t(f(X(t))-f^\star)\,dt\leq\frac{(r-1)^2\|x_0-x^\star\|^2}{2(r-3)}.$$
--
--   The integral estimate controls the accumulated objective error and is stronger than integrating the pointwise rate alone.
--
--   **Formalization Note** A positive $L$ witnesses $f\in\mathcal F_\infty$. Integrability on $(0,\infty)$ is explicitly part of the conclusion, so the improper integral cannot receive a default value for a nonintegrable function. The estimate holds for every solution in the stated regularity class.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, pp. 12–13, Theorem 5

import Mathlib
import Definitions.Def_NesterovODE_StrongCvx_Setting

namespace NesterovODE.StrongCvx

/-- The two estimates of Theorem 5. -/
theorem theorem_5 (n : ℕ) (f : NesterovODE.WellPosed.E n → ℝ) (L : NNReal) (r : ℝ)
    (x₀ xstar : NesterovODE.WellPosed.E n) (X V : ℝ → NesterovODE.WellPosed.E n)
    (hL : 0 < L) (hf : InFL L f) (hr : 3 < r)
    (hmin : ∀ y, f xstar ≤ f y)
    (hX : IsSolution f r x₀ X V) :
    (∀ t : ℝ, 0 < t →
      f (X t) - f xstar ≤
        (r - 1) ^ 2 * ‖x₀ - xstar‖ ^ 2 / (2 * t ^ 2)) ∧
    MeasureTheory.IntegrableOn (fun t : ℝ => t * (f (X t) - f xstar)) (Set.Ioi 0) ∧
    (∫ t in Set.Ioi (0 : ℝ), t * (f (X t) - f xstar)) ≤
      (r - 1) ^ 2 * ‖x₀ - xstar‖ ^ 2 / (2 * (r - 3)) := by sorry

end NesterovODE.StrongCvx
