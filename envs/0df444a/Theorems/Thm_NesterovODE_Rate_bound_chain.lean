-- Prove2me | Theorems.Thm_NesterovODE_Rate_bound_chain
-- name    : NesterovODE.Rate.bound_chain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:49:06.085572+00:00
-- url     : https://prove2.me/theorems/3abce924-ed59-4645-91f9-e6797feddda6
-- title:
--   p. 8, proof of Theorem 3 — E is nonincreasing and f(X(t)) − f⋆ ≤ E(t)/t² ≤ E(0)/t² = 2‖x₀ − x⋆‖²/t²
-- statement:
--   Let $f\in\mathcal F_\infty$ on $\mathbb R^n$, let $x^\star$ be a minimizer of $f$ with $f^\star=f(x^\star)$, let $X$ be a solution of (3) with $X(0)=x_0$, $\dot X(0)=0$, and let $\mathcal E$ be the energy of Theorem 3's proof. Then:
--
--   1. $\mathcal E$ is nonincreasing on $[0,\infty)$;
--   2. for every $t>0$,
--   $$f(X(t))-f^\star\le\frac{\mathcal E(t)}{t^2}\le\frac{\mathcal E(0)}{t^2}=\frac{2\|x_0-x^\star\|^2}{t^2}.$$
--
--   The first inequality uses only $2\|X+t\dot X/2-x^\star\|^2\ge0$; the second is the monotonicity of the energy, and the equality evaluates $\mathcal E(0)$ from $X(0)=x_0$.
--
--   **Formalization Note** $\mathcal E(0)$ is the energy formula evaluated at $t=0$, $0\cdot(\dots)+2\|x_0+0-x^\star\|^2$. Monotonicity on the closed half-line $[0,\infty)$ includes the endpoint $t=0$, where the solution is only right-continuous.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, p. 8, proof of Theorem 3 (second display)

import Mathlib
import Definitions.Def_NesterovODE_Rate_Setting

namespace NesterovODE.Rate

/-- Proof of Theorem 3, p. 8: the energy is nonincreasing on `[0, ∞)`, and for every `t > 0`,
`f(X(t)) − f⋆ ≤ E(t)/t² ≤ E(0)/t² = 2‖x₀ − x⋆‖²/t²`. -/
theorem bound_chain {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsFinfty f)
    (x₀ xstar : EuclideanSpace ℝ (Fin n)) (hxstar : ∀ y, f xstar ≤ f y)
    (X V : ℝ → EuclideanSpace ℝ (Fin n)) (hX : IsSolution f 3 x₀ X V) :
    AntitoneOn (energy f xstar X V) (Set.Ici 0) ∧
      ∀ t : ℝ, 0 < t →
        f (X t) - f xstar ≤ energy f xstar X V t / t ^ 2 ∧
        energy f xstar X V t / t ^ 2 ≤ energy f xstar X V 0 / t ^ 2 ∧
        energy f xstar X V 0 / t ^ 2 = 2 * ‖x₀ - xstar‖ ^ 2 / t ^ 2 := by sorry

end NesterovODE.Rate
