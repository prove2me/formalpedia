-- Prove2me | Theorems.Thm_NonsmoothQN_ExactNorm_prop_3_3_spiral
-- name    : NonsmoothQN.ExactNorm.prop_3_3_spiral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:07.419618+00:00
-- url     : https://prove2.me/theorems/d83eb5de-72ff-416d-af62-eaf57421ae85
-- title:
--   Proposition 3.3, p. 143 — BFGS from x₀ = [1;0], H₀ = [[3,−√3],[−√3,3]] turns by π/3 and halves every step (orientation corrected)
-- statement:
--   Apply the quasi-Newton method (Algorithm 2.1) with the BFGS update (2.2) and an exact line search to the Euclidean norm on $\mathbb R^2$, starting from
--   $$x_0 = \begin{bmatrix}1\\0\end{bmatrix},\qquad H_0 = \begin{bmatrix}3 & -\sqrt3\\ -\sqrt3 & 3\end{bmatrix}.$$
--   Then:
--
--   1. the method is well defined and never stops: there is a run of Algorithm 2.1 from these data, with every $H_k$ positive definite, every step exact and positive, and every $H_{k+1}$ the BFGS update of $H_k$;
--   2. every such run satisfies, for all $k \ge 0$,
--   $$x_k = 2^{-k}\begin{bmatrix}\cos(k\pi/3)\\ \sin(k\pi/3)\end{bmatrix},$$
--   so the iterates rotate counterclockwise through the angle $\pi/3$ and shrink by the factor $1/2$ at each iteration.
--
--   This explicit run shows that the rate $1/2$ and the turn $\pi/3$ of Theorem 3.2 are attained exactly, and it witnesses that the hypotheses of Theorem 3.2 can be met.
--
--   **Formalization Note.** The page says the iterates "rotate clockwise". That is a slip: $p_0 = -H_0x_0 = [-3;\sqrt3]$, the exact step is $t_0 = 1/4$, and $x_1 = [1/4;\sqrt3/4]$, a counterclockwise turn in the standard orientation; the Lean states the counterclockwise formula. The BFGS update is the published `ShannoCG.SCONB.bfgsUpdate H σ y` with the step $\sigma = t_kp_k$ and $y_k = \nabla f(x_{k+1})-\nabla f(x_k)$; expanding $V_kH_kV_k^T + t_k(p_k^Ty_k)^{-1}p_kp_k^T$ with $V_k = I-(p_k^Ty_k)^{-1}p_ky_k^T$ gives exactly Shanno's additive form, for every $H_k$. The existence clause (1) is the page's "the method generates a sequence".
-- source:
--   Lewis, Overton, Nonsmooth optimization via quasi-Newton methods, Math. Program. Ser. A 141 (2013) 135–163, p. 143, Proposition 3.3 (with the BFGS update (2.2), p. 140)

import Mathlib
import Definitions.Def_NonsmoothQN_ExactNorm_Basic
import Definitions.Def_ShannoCG_SCONB_bfgsUpdate

open Matrix Filter Topology

namespace NonsmoothQN.ExactNorm

theorem prop_3_3_spiral :
    (∃ (x : ℕ → Fin 2 → ℝ) (H : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (t : ℕ → ℝ),
      IsExactNormRun x H t ∧ x 0 = ![1, 0] ∧
        H 0 = !![3, -Real.sqrt 3; -Real.sqrt 3, 3] ∧
        ∀ k, H (k + 1) = ShannoCG.SCONB.bfgsUpdate (H k) (t k • qnDir (H k) (x k))
          (gradNorm (x (k + 1)) - gradNorm (x k))) ∧
    ∀ (x : ℕ → Fin 2 → ℝ) (H : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (t : ℕ → ℝ),
      IsExactNormRun x H t → x 0 = ![1, 0] →
        H 0 = !![3, -Real.sqrt 3; -Real.sqrt 3, 3] →
        (∀ k, H (k + 1) = ShannoCG.SCONB.bfgsUpdate (H k) (t k • qnDir (H k) (x k))
          (gradNorm (x (k + 1)) - gradNorm (x k))) →
        ∀ k : ℕ, x k = ((1 : ℝ) / 2) ^ k •
          ![Real.cos (k * Real.pi / 3), Real.sin (k * Real.pi / 3)] := by sorry

end NonsmoothQN.ExactNorm
