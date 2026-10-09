-- Prove2me | Theorems.Thm_IQCAlg_HeavyBall_tail_bound
-- name    : IQCAlg.HeavyBall.tail_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:03.121304+00:00
-- url     : https://prove2.me/theorems/a025c035-dbb6-46d1-800e-5e22b8c84629
-- title:
--   Appendix B, p. 40 — eight consecutive ε² < ε̄² (ε̄ = r − 2) force ε²_k < ε̄² for the whole tail
-- statement:
--   Let $(x_k)$ satisfy (B.1), let $\varepsilon_k=x_k-x^\star_k$, and let $\bar\varepsilon=r-2=142/1225$, the distance from the cycle (B.3) to the nearest transition point $1$ or $2$ of (4.11). If for some $i$
--   $$\varepsilon_{i+j}^2<\bar\varepsilon^2\qquad (j=0,1,\dots,7),$$
--   then $\varepsilon_k^2<\bar\varepsilon^2$ for every $k\ge i$.
--
--   Once eight consecutive iterates are within $\bar\varepsilon$ of the cycle, all later iterates stay on the cycle's pieces, so the linear perturbation recursion applies forever after.
--
--   **Formalization Note** The page first says "some $\bar\varepsilon$" and then fixes $\bar\varepsilon=r-2$; the statement uses that value.
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, p. 40, the paragraph after (B.4)

import Mathlib
import Definitions.Def_IQCAlg_HeavyBall_Setting

namespace IQCAlg.HeavyBall

/-- Tail argument, p. 40: if `x` satisfies (B.1) and eight consecutive perturbations
`ε_i, …, ε_{i+7}` have `ε² < ε̄²` with `ε̄ = r − 2`, then `ε_k² < ε̄²` for every `k ≥ i`. -/
theorem tail_bound (x : ℕ → ℝ) (hx : IsB1Traj x) (i : ℕ)
    (h8 : ∀ j : ℕ, j < 8 → eps x (i + j) ^ 2 < epsBar ^ 2) :
    ∀ k : ℕ, i ≤ k → eps x k ^ 2 < epsBar ^ 2 := by sorry

end IQCAlg.HeavyBall
