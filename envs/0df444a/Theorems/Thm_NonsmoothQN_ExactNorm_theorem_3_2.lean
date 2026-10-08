-- Prove2me | Theorems.Thm_NonsmoothQN_ExactNorm_theorem_3_2
-- name    : NonsmoothQN.ExactNorm.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:58.670594+00:00
-- url     : https://prove2.me/theorems/841af0aa-bed9-4a3d-a851-3675aaf6efb3
-- title:
--   Theorem 3.2, p. 142 — exact line search on ‖·‖ in ℝ²: Q-linear rate 1/2, turns → π/3, eventually consistent orientation
-- statement:
--   Consider the quasi-Newton method (Algorithm 2.1) with an exact line search applied to the Euclidean norm $f(x) = \|x\|$ on $\mathbb R^2$: from $x_0 \neq 0$, at each iteration $p_k = -H_k\nabla f(x_k)$ with $H_k$ symmetric positive definite, $x_{k+1} = x_k + t_kp_k$ where $t_k > 0$ minimizes $t \mapsto \|x_k + tp_k\|$, and $H_{k+1}$ is any symmetric positive definite matrix satisfying the secant condition $H_{k+1}(\nabla f(x_{k+1}) - \nabla f(x_k)) = t_kp_k$. Suppose the algorithm does not terminate, i.e. $x_k \neq 0$ for every $k$. Then
--
--   1. $\|x_k\| \to 0$ Q-linearly with rate $1/2$:
--   $$\|x_k\|\to 0, \qquad \frac{\|x_{k+1}\|}{\|x_k\|} \to \frac12 ;$$
--   2. the angle between consecutive iterates tends to $\pi/3$:
--   $$\angle(x_k, x_{k+1}) \to \frac{\pi}{3};$$
--   3. the rotation eventually has a consistent orientation: there is $\sigma \in \{1,-1\}$ with $\sigma\,\operatorname{cross}(x_k,x_{k+1}) > 0$ for all sufficiently large $k$ (all eventually counterclockwise, or all eventually clockwise).
--
--   This is the paper's first convergence theorem for a quasi-Newton method on a nonsmooth function: whatever positive definite secant update is used, the iterates spiral into the nondifferentiable minimizer at a fixed linear rate.
--
--   **Formalization Note.** "The sequence of iterates converges to zero at Q-linear rate 1/2" is read through the real sequence $\|x_k\|$, following the proof's last line ("the ratio $\|x_{k+1}\|/\|x_k\|$ approaches $1/2$, showing Q-linear convergence"). Norms are Euclidean (`eucNorm`), not Lean's default sup norm on `Fin 2 → ℝ`. Angles are unsigned; orientation is the sign of $\operatorname{cross}(u,v) = u_1v_2-u_2v_1$. The run is `IsExactNormRun`; the update is not restricted to BFGS.
-- source:
--   Lewis, Overton, Nonsmooth optimization via quasi-Newton methods, Math. Program. Ser. A 141 (2013) 135–163, p. 142, Theorem 3.2

import Mathlib
import Definitions.Def_NonsmoothQN_ExactNorm_Basic

open Matrix Filter Topology

namespace NonsmoothQN.ExactNorm

theorem theorem_3_2 (x : ℕ → Fin 2 → ℝ) (H : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (t : ℕ → ℝ)
    (hrun : IsExactNormRun x H t) (hnt : ∀ k, x k ≠ 0) :
    IsQLinear (fun k => eucNorm (x k)) 0 (1 / 2) ∧
      Tendsto (fun k => turnAngle (x k) (x (k + 1))) atTop (𝓝 (Real.pi / 3)) ∧
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ᶠ k in atTop, 0 < σ * cross (x k) (x (k + 1)) := by sorry

end NonsmoothQN.ExactNorm
