-- Prove2me | Theorems.Thm_ModernConvex_MatrixCube_theta_bounds
-- name    : ModernConvex.MatrixCube.theta_bounds
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:44.922678+00:00
-- url     : https://prove2.me/theorems/0d7d222b-9259-46c3-85ce-0cf6f4dd66b3
-- title:
--   Eq. (4.4.37) — θ(k) ≤ π√k/2 for k ≥ 1, and θ(2) = π/2
-- statement:
--   Let $\theta$ be the function (4.4.38),
--   $$\theta(k)=\frac{1}{\min\left\{\int_{\mathbb R^k}|\alpha_1u_1^2+\cdots+\alpha_ku_k^2|\,p_k(u)\,du \;\middle|\; \alpha\in\mathbb R^k,\ \|\alpha\|_1=1\right\}},$$
--   with $p_k$ the standard Gaussian density on $\mathbb R^k$. Then
--   $$\theta(k)\le\frac{\pi\sqrt k}{2}\quad(k\ge1),\qquad \theta(2)=\frac{\pi}{2}.$$
--
--   These bounds turn the Matrix Cube Theorem into explicit approximation ratios: at most $\pi\sqrt\mu/2$ in general and exactly the factor $\pi/2$ when all $A_i$ have rank at most $2$ (the interval Lyapunov application).
--
--   **Formalization Note** The constants are exact: $\pi\sqrt k/2$ and $\pi/2$. The statement is part (ii) of the proof of Theorem 4.4.1 (pp. 193–194), labelled (4.4.37) in the theorem.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 190, Eq. (4.4.37) in Theorem 4.4.1; proof pp. 193–194

import Mathlib
import Definitions.Def_ModernConvex_MatrixCube_MatrixCube

namespace ModernConvex.MatrixCube

/-- Ben-Tal–Nemirovski, (4.4.37), p. 190 (proved as part (ii) of Theorem 4.4.1, pp. 193–194):
the function `θ` of (4.4.38) satisfies `θ(k) ≤ π√k/2` for every `k ≥ 1`, and `θ(2) = π/2`. -/
theorem theta_bounds :
    (∀ k : ℕ, 1 ≤ k → theta k ≤ Real.pi * Real.sqrt k / 2) ∧ theta 2 = Real.pi / 2 := by sorry

end ModernConvex.MatrixCube
