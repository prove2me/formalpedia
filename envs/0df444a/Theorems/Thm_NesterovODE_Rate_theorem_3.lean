-- Prove2me | Theorems.Thm_NesterovODE_Rate_theorem_3
-- name    : NesterovODE.Rate.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:48:54.053149+00:00
-- url     : https://prove2.me/theorems/b07c1a43-f043-453d-bb3d-397324391ffb
-- title:
--   Theorem 3, p. 7 — for f ∈ F_∞ the solution of (3) satisfies f(X(t)) − f⋆ ≤ 2‖x₀ − x⋆‖²/t²
-- statement:
--   Let $f\in\mathcal F_\infty$, i.e. $f:\mathbb R^n\to\mathbb R$ is convex and continuously differentiable with $L$-Lipschitz gradient for some $L>0$. Let $x^\star$ be any minimizer of $f$ and $f^\star=f(x^\star)$. Let $X$ be the solution of
--   $$\ddot X+\frac3t\dot X+\nabla f(X)=0\quad(t>0),\qquad X(0)=x_0,\ \dot X(0)=0 .$$
--   Then for every $t>0$,
--   $$f(X(t))-f^\star\le\frac{2\|x_0-x^\star\|^2}{t^2}.\tag{7}$$
--
--   This is the continuous-time counterpart of Nesterov's bound $f(x_k)-f^\star\le 2\|x_0-x^\star\|^2/(s(k+1)^2)$ for the accelerated gradient method with step size $s\le1/L$ (6): under the identification $t\approx k\sqrt s$ the two rates coincide.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`. The paper speaks of "the unique global solution" in $C^2((0,\infty))\cap C^1([0,\infty))$; the statement here holds for every solution in that class (encoded as a pair $(X,\dot X)$), which by Theorem 1 of the paper is the same statement. No hypothesis beyond the paper's is added; the Lipschitz constant is not used quantitatively.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, p. 7, Theorem 3, (7)

import Mathlib
import Definitions.Def_NesterovODE_Rate_Setting

namespace NesterovODE.Rate

/-- Theorem 3 (arXiv:1503.01243v2, p. 7): for `f ∈ F_∞`, every minimizer `x⋆` and every solution
`X` of (3) with `X(0) = x₀`, `Ẋ(0) = 0`, one has `f(X(t)) − f⋆ ≤ 2‖x₀ − x⋆‖²/t²` for all `t > 0`. -/
theorem theorem_3 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsFinfty f)
    (x₀ xstar : EuclideanSpace ℝ (Fin n)) (hxstar : ∀ y, f xstar ≤ f y)
    (X V : ℝ → EuclideanSpace ℝ (Fin n)) (hX : IsSolution f 3 x₀ X V) :
    ∀ t : ℝ, 0 < t → f (X t) - f xstar ≤ 2 * ‖x₀ - xstar‖ ^ 2 / t ^ 2 := by sorry

end NesterovODE.Rate
