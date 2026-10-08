-- Prove2me | Theorems.Thm_NonsmoothQN_ExactNorm_exact_step_geometry
-- name    : NonsmoothQN.ExactNorm.exact_step_geometry
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:00.321635+00:00
-- url     : https://prove2.me/theorems/985c7df3-6944-4876-a94e-a981c18e0a76
-- title:
--   §3.1, proof of Theorem 3.2, p. 142 — content of the normalized display for x_{k+1}: ‖x_{k+1}‖ = ‖x_k‖ sin θ_k, turn π/2 − θ_k
-- statement:
--   Let $x \in \mathbb R^2$ be nonzero and let $p \in \mathbb R^2$ be a descent direction for the Euclidean norm at $x$, that is $p^T x < 0$. Let $t$ minimize $\tau \mapsto \|x + \tau p\|$ over $\tau \in \mathbb R$ and put $x^+ = x + t p$, and assume $x^+ \neq 0$. Let $\theta$ be the angle between $p$ and $-x$. Then
--
--   1. $0 < \theta < \pi/2$;
--   2. the new iterate has norm
--   $$\|x^+\| = \|x\|\,\sin\theta ;$$
--   3. the angle between $x$ and $x^+$ is $\pi/2 - \theta$;
--   4. $x^+$ lies on the same side of the line $\mathbb R x$ as $p$: $\operatorname{cross}(x,x^+)$ and $\operatorname{cross}(x,p)$ have the same (nonzero) sign.
--
--   This is the coordinate-free content of the display on p. 142, which normalizes $x_k = [1;0]$ and $p_k = [-\cos\theta_k;\sin\theta_k]$ and obtains $x_{k+1} = [\sin^2\theta_k;\sin\theta_k\cos\theta_k]$ from the exactness of the line search. It describes one exact step of the quasi-Newton method on the norm.
--
--   **Formalization Note.** The page states the display after a rotation and scaling ("without loss of generality"); the Lean states its invariant content for arbitrary $x \neq 0$ instead. The hypothesis $x^+ \neq 0$ is the page's "the algorithm does not terminate", which gives $\theta>0$. Angles are unsigned, $\arccos$ of the normalized inner product; $\operatorname{cross}(u,v) = u_1v_2 - u_2v_1$; norms are Euclidean.
-- source:
--   Lewis, Overton, Nonsmooth optimization via quasi-Newton methods, Math. Program. Ser. A 141 (2013) 135–163, p. 142, §3.1, proof of Theorem 3.2, definition of θ_k and the display for x_{k+1}

import Mathlib
import Definitions.Def_NonsmoothQN_ExactNorm_Basic

open Matrix Filter Topology

namespace NonsmoothQN.ExactNorm

theorem exact_step_geometry (x p : Fin 2 → ℝ) (t : ℝ)
    (hx : x ≠ 0) (hdesc : p ⬝ᵥ x < 0)
    (hexact : ∀ τ : ℝ, eucNorm (x + t • p) ≤ eucNorm (x + τ • p))
    (hnt : x + t • p ≠ 0) :
    0 < turnAngle p (-x) ∧ turnAngle p (-x) < Real.pi / 2 ∧
      eucNorm (x + t • p) = eucNorm x * Real.sin (turnAngle p (-x)) ∧
      turnAngle x (x + t • p) = Real.pi / 2 - turnAngle p (-x) ∧
      0 < cross x (x + t • p) * cross x p := by sorry

end NonsmoothQN.ExactNorm
