-- Prove2me | Theorems.Thm_IQCAlg_HeavyBall_eq_B_4
-- name    : IQCAlg.HeavyBall.eq_B_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:20:52.304984+00:00
-- url     : https://prove2.me/theorems/2c305310-5af2-4ef8-b47b-e31e664d103c
-- title:
--   (B.4), p. 40 — ε²_{k+8} < (1/2)(ε²_{k+1} + ε²_k) while the iterates stay on the cycle's pieces
-- statement:
--   Let $(x_k)$ satisfy (B.1), let $\varepsilon_k=x_k-x^\star_k$ be its perturbation from the cycle (B.3), and fix $k$. Assume that each of $x_{k+1},\dots,x_{k+7}$ lies on the same linear piece of (4.11) as the corresponding $x^\star$ (if $x^\star_j<1$ then $x_j<1$; if $x^\star_j>2$ then $x_j>2$), and that $(\varepsilon_{k+1},\varepsilon_k)\neq(0,0)$. Then
--   $$\varepsilon_{k+8}^2<\tfrac12\bigl(\varepsilon_{k+1}^2+\varepsilon_k^2\bigr).$$
--
--   This is the eight-step contraction of the perturbation that drives the tail argument.
--
--   **Formalization Note** Two departures from the printed (B.4), both disclosed. (i) The page's strict inequality fails when $\varepsilon_k=\varepsilon_{k+1}=0$ (it would read $0<0$), so $(\varepsilon_{k+1},\varepsilon_k)\neq0$ is assumed. (ii) The page's middle terms involve $\varepsilon_{k+9}$, which would need the same-piece condition at $k+8$ as well; the statement keeps only the outer inequality, which needs the condition at $k+1,\dots,k+7$ (since $\varepsilon_{k+8}$ is the second entry of $P^8(\varepsilon_{k+1},\varepsilon_k)$).
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, p. 40, (B.4)

import Mathlib
import Definitions.Def_IQCAlg_HeavyBall_Setting

namespace IQCAlg.HeavyBall

/-- (B.4), p. 40: if `x` satisfies (B.1), the iterates `x_{k+1}, …, x_{k+7}` lie on the same
pieces of (4.11) as the cycle, and `(ε_{k+1}, ε_k) ≠ 0`, then
`ε²_{k+8} < (1/2)(ε²_{k+1} + ε²_k)`. -/
theorem eq_B_4 (x : ℕ → ℝ) (hx : IsB1Traj x) (k : ℕ)
    (hpiece : ∀ j : ℕ, 1 ≤ j → j ≤ 7 →
      (cyc (k + j) < 1 → x (k + j) < 1) ∧ (2 < cyc (k + j) → 2 < x (k + j)))
    (hne : eps x k ≠ 0 ∨ eps x (k + 1) ≠ 0) :
    eps x (k + 8) ^ 2 < 1 / 2 * (eps x (k + 1) ^ 2 + eps x k ^ 2) := by sorry

end IQCAlg.HeavyBall
