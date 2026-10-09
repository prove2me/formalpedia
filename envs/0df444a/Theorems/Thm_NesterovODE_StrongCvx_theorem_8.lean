-- Prove2me | Theorems.Thm_NesterovODE_StrongCvx_theorem_8
-- name    : NesterovODE.StrongCvx.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:37:07.685442+00:00
-- url     : https://prove2.me/theorems/f32fc615-a476-4831-a02a-d0edc39e49ab
-- title:
--   Theorem 8, p. 17 — accelerated rate for the strongly convex ODE
-- statement:
--   Fix real numbers $r$ and $\alpha$ with $2\leq\alpha\leq2r/3$. There exists a constant $C$ depending only on $r$ and $\alpha$ such that, in every dimension, for every $\mu>0$, $L>0$, $f\in\mathcal S_{\mu,L}$, minimizer $x^\star$, initial point $x_0$, solution $(X,V)$ of (17), and $t>0$,
--
--   $$f(X(t))-f^\star\leq\frac{C\|x_0-x^\star\|^2}{\mu^{(\alpha-2)/2}t^\alpha}.$$
--
--   This gives the paper's improved polynomial rate when the damping and strong convexity are combined. The constant is uniform over functions, dimensions, strong-convexity parameters, smoothness parameters, initial data, solutions, and time.
--
--   **Formalization Note** The condition $\mu>0$ is implicit in the paper's denominator and threshold time. The statement ranges over every solution in the ODE regularity class, avoiding dependence on an unproved uniqueness assertion for general $r$.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, p. 17, Theorem 8

import Mathlib
import Definitions.Def_NesterovODE_StrongCvx_Setting

namespace NesterovODE.StrongCvx

/-- Theorem 8: a constant uniform in dimension, smoothness, strong convexity, and trajectory. -/
theorem theorem_8 (r α : ℝ) (ha : 2 ≤ α) (hr : α ≤ 2 * r / 3) :
    ∃ C : ℝ, ∀ (n : ℕ) (f : NesterovODE.WellPosed.E n → ℝ) (mu : ℝ) (L : NNReal),
      0 < mu → 0 < L → InSMuL mu L f →
      ∀ (x₀ xstar : NesterovODE.WellPosed.E n), (∀ y, f xstar ≤ f y) →
      ∀ (X V : ℝ → NesterovODE.WellPosed.E n), IsSolution f r x₀ X V →
      ∀ t : ℝ, 0 < t →
        f (X t) - f xstar ≤
          C * ‖x₀ - xstar‖ ^ 2 / (mu ^ ((α - 2) / 2) * t ^ α) := by sorry

end NesterovODE.StrongCvx
