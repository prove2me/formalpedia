-- Prove2me | Theorems.Thm_NonsmoothQN_Secant_secant_H_and_direction
-- name    : NonsmoothQN.Secant.secant_H_and_direction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:48.842777+00:00
-- url     : https://prove2.me/theorems/9d47eff7-9f8b-4d5b-8db8-56e3fb2d9b97
-- title:
--   §5.1, p. 152 — $H_{k+1}=|x_{k+1}-x_k|/2$ and $p_{k+1}=-\frac{|x_{k+1}-x_k|}{2}\operatorname{sgn}(x_{k+1})$
-- statement:
--   Run the secant method on $f(x)=|x|$ with the inexact line search of §5.1, from any $x_0$ and any $H_0>0$. For every $k$ with $x_k\ne0$ and $x_{k+1}\ne0$, the inverse Hessian approximation given by the secant equation and the next search direction are
--   $$H_{k+1}=\frac{|x_{k+1}-x_k|}{2},\qquad p_{k+1}=-\frac{|x_{k+1}-x_k|}{2}\,\operatorname{sgn}(x_{k+1}),$$
--   and the iterates alternate in sign: $x_kx_{k+1}<0$.
--
--   So the search direction always points back across zero with length half the distance to the previous iterate; this is what reduces the method to a bisection scheme.
--
--   **Formalization Note** The page assumes the setting of Algorithm 2.1, where $H_0$ is positive definite, i.e. $H_0>0$; this is the only hypothesis. The conditions $x_k\ne0\ne x_{k+1}$ are the page's ("providing $x_k\ne0\ne x_{k+1}$"); a run with $x_k=0$ has already stopped.
-- source:
--   Lewis, Overton, Nonsmooth optimization via quasi-Newton methods, Math. Program. Ser. A 141 (2013) 135–163, p. 152, §5.1, first display

import Mathlib
import Definitions.Def_NonsmoothQN_Secant_Basic
import Definitions.Def_NonsmoothQN_Secant_Expansion

namespace NonsmoothQN.Secant

theorem secant_H_and_direction (x₀ H₀ : ℝ) (hH₀ : 0 < H₀) (k : ℕ)
    (hk : secX x₀ H₀ k ≠ 0) (hk1 : secX x₀ H₀ (k + 1) ≠ 0) :
    secH x₀ H₀ (k + 1) = |secX x₀ H₀ (k + 1) - secX x₀ H₀ k| / 2 ∧
    secP x₀ H₀ (k + 1) =
      -(|secX x₀ H₀ (k + 1) - secX x₀ H₀ k| / 2) * Real.sign (secX x₀ H₀ (k + 1)) ∧
    secX x₀ H₀ k * secX x₀ H₀ (k + 1) < 0 := by sorry

end NonsmoothQN.Secant
