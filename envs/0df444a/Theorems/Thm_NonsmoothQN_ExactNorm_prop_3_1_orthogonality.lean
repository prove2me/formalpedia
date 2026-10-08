-- Prove2me | Theorems.Thm_NonsmoothQN_ExactNorm_prop_3_1_orthogonality
-- name    : NonsmoothQN.ExactNorm.prop_3_1_orthogonality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:04.885955+00:00
-- url     : https://prove2.me/theorems/8b1c255d-450b-4a92-bae8-9a765d1431ba
-- title:
--   Proposition 3.1, p. 141 — exact line search ⇒ next search direction is orthogonal to y_k
-- statement:
--   Consider one iteration of a quasi-Newton method (Algorithm 2.1) for a function $f:\mathbb R^n\to\mathbb R$. Let $H_k$ be symmetric positive definite, let $f$ be differentiable at $x_k$ with gradient $\nabla f_k$, put $p_k = -H_k\nabla f_k$, and let $t_k>0$ and $x_{k+1} = x_k + t_k p_k$. Suppose that
--
--   1. the function $t \mapsto f(x_k + t p_k)$ has a local minimizer at $t_k$;
--   2. $f$ is differentiable at $x_{k+1}$, with gradient $\nabla f_{k+1}$;
--   3. $H_{k+1}$ is symmetric positive definite and satisfies the secant condition $H_{k+1} y_k = t_k p_k$, where $y_k = \nabla f_{k+1} - \nabla f_k$.
--
--   Then the next search direction $p_{k+1} = -H_{k+1}\nabla f_{k+1}$ satisfies
--   $$p_{k+1}^T y_k = 0 .$$
--
--   This orthogonality is the only property of the exact line search used in the analysis of the norm in the plane: it fixes the direction of $p_{k+1}$ up to sign.
--
--   **Formalization Note.** The statement is for general dimension $n$ and general $f$. The gradient $g$ at $x$ means: $f$ is differentiable at $x$ and its Fréchet derivative is $v\mapsto g^Tv$ (`IsGradAt`). The algorithm's standing data (positive definite $H_k$, $p_k=-H_k\nabla f_k$, $t_k>0$, $x_{k+1}=x_k+t_kp_k$) are hypotheses; the symmetry of $H_{k+1}$, part of positive definiteness, is needed.
-- source:
--   Lewis, Overton, Nonsmooth optimization via quasi-Newton methods, Math. Program. Ser. A 141 (2013) 135–163, p. 141, Proposition 3.1 (with Algorithm 2.1, p. 140)

import Mathlib
import Definitions.Def_NonsmoothQN_ExactNorm_Basic

open Matrix Filter Topology

namespace NonsmoothQN.ExactNorm

theorem prop_3_1_orthogonality {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (xk pk gk xk1 gk1 : Fin n → ℝ) (Hk Hk1 : Matrix (Fin n) (Fin n) ℝ) (tk : ℝ)
    (hHk : Hk.PosDef) (hHk1 : Hk1.PosDef)
    (hgk : IsGradAt f gk xk) (hpk : pk = -(Hk *ᵥ gk))
    (htk : 0 < tk) (hxk1 : xk1 = xk + tk • pk)
    (hmin : IsLocalMin (fun τ : ℝ => f (xk + τ • pk)) tk)
    (hgk1 : IsGradAt f gk1 xk1)
    (hsec : Hk1 *ᵥ (gk1 - gk) = tk • pk) :
    (-(Hk1 *ᵥ gk1)) ⬝ᵥ (gk1 - gk) = 0 := by sorry

end NonsmoothQN.ExactNorm
