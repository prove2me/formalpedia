-- Prove2me | Theorems.Thm_NonsmoothQN_ExactNorm_sin_angle_recursion
-- name    : NonsmoothQN.ExactNorm.sin_angle_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:56.021747+00:00
-- url     : https://prove2.me/theorems/c3b3136e-751c-453d-acb9-7f827aa4d5c5
-- title:
--   §3.1, proof of Theorem 3.2, p. 142 — sin θ_{k+1} = √((1 − sin θ_k)/2)
-- statement:
--   Consider a run of the quasi-Newton method (Algorithm 2.1) with an exact line search applied to the Euclidean norm on $\mathbb R^2$: iterates $x_k$, symmetric positive definite matrices $H_k$ satisfying the secant condition, and exact steps $t_k>0$. Suppose the method does not terminate, i.e. $x_k \neq 0$ for all $k$. Let $\theta_k$ be the angle between the search direction $p_k = -H_k \nabla f(x_k)$ and the vector $-x_k$. Then for every $k$,
--   $$\sin\theta_{k+1} = \sqrt{\frac{1-\sin\theta_k}{2}} .$$
--
--   This recursion reduces the planar dynamics of the method to a one-dimensional iteration, independent of the particular secant update chosen.
--
--   **Formalization Note.** The run is `IsExactNormRun` (see the definition item); $\theta_k$ is the unsigned angle $\arccos$ of the normalized inner product of $p_k$ and $-x_k$. Only the outer equality of the page's chain of equalities is stated.
-- source:
--   Lewis, Overton, Nonsmooth optimization via quasi-Newton methods, Math. Program. Ser. A 141 (2013) 135–163, p. 142, §3.1, proof of Theorem 3.2, the display for sin θ_{k+1}

import Mathlib
import Definitions.Def_NonsmoothQN_ExactNorm_Basic

open Matrix Filter Topology

namespace NonsmoothQN.ExactNorm

theorem sin_angle_recursion (x : ℕ → Fin 2 → ℝ) (H : ℕ → Matrix (Fin 2) (Fin 2) ℝ)
    (t : ℕ → ℝ) (hrun : IsExactNormRun x H t) (hnt : ∀ k, x k ≠ 0) (k : ℕ) :
    Real.sin (turnAngle (qnDir (H (k + 1)) (x (k + 1))) (-(x (k + 1)))) =
      angleMap (Real.sin (turnAngle (qnDir (H k) (x k)) (-(x k)))) := by sorry

end NonsmoothQN.ExactNorm
