-- Prove2me | Theorems.Thm_IQCAlg_HeavyBall_iterates_4_to_11
-- name    : IQCAlg.HeavyBall.iterates_4_to_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:04.915837+00:00
-- url     : https://prove2.me/theorems/b3edcbce-5161-487f-ac09-5104bc5dbd5d
-- title:
--   Appendix B, p. 40 — from x₀ = 3.3, |x_j − x⋆_j| < ε̄ for j = 4, …, 11
-- statement:
--   Run the Heavy-ball method $x_{k+1}=x_k-\alpha\nabla f(x_k)+\beta(x_k-x_{k-1})$ with the gradient (4.11), the tuning of Proposition 1 at $L=25$, $m=1$ (i.e. $\alpha=4/(\sqrt{25}+\sqrt1)^2$, $\beta=((\sqrt{25}-1)/(\sqrt{25}+1))^2$), the starting point $x_0=3.3$ and the initialization $x_{-1}=x_0$. Then
--   $$|x_j-x^\star_j|<\bar\varepsilon=\tfrac{142}{1225}\qquad (j=4,5,\dots,11),$$
--   where $x^\star$ is the cycle $p,q,r,p,\dots$ of (B.3).
--
--   This supplies the eight consecutive iterates required by the tail argument.
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, p. 40, "if x₀ = 3.3, then the iterates x₄, x₅, …, x₁₁ are each within a distance ε̄ of their respective limit points"

import Mathlib
import Definitions.Def_IQCAlg_HeavyBall_Setting

namespace IQCAlg.HeavyBall

/-- p. 40: for the Heavy-ball run from `x_0 = 3.3` (with `x_{−1} = x_0`) with Proposition 1's
tuning at `L = 25`, `m = 1`, on the gradient (4.11), the iterates `x_4, …, x_11` are each
within `ε̄` of their limit points `x⋆_k`. -/
theorem iterates_4_to_11 :
    ∀ j : ℕ, 4 ≤ j → j ≤ 11 →
      |hbRun gradF (hbAlpha 25 1) (hbBeta 25 1) (33 / 10) j - cyc j| < epsBar := by sorry

end IQCAlg.HeavyBall
