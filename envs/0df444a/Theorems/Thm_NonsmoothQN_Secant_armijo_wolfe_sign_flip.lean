-- Prove2me | Theorems.Thm_NonsmoothQN_Secant_armijo_wolfe_sign_flip
-- name    : NonsmoothQN.Secant.armijo_wolfe_sign_flip
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:46.498974+00:00
-- url     : https://prove2.me/theorems/798c50d3-c0cc-4f9e-a470-0a51cba3d4be
-- title:
--   §5.1, pp. 151–152 — A and W give $|x_{k+1}|<|x_k|$ and $x_kx_{k+1}<0$ when $x_k\ne0\ne x_{k+1}$
-- statement:
--   Let $x\ne0$ be an iterate and $p$ a search direction with $px<0$, and let $t$ be a step satisfying the two line search conditions of §5.1,
--   $$-\frac{x}{p}\le t<-\frac{2x}{p}.$$
--   If the new point $x^+=x+tp$ is nonzero, then
--   $$|x^+|<|x|\qquad\text{and}\qquad x\,x^+<0 .$$
--
--   Applied to $x=x_k$, $p=p_k$, $t=t_k$, this says that every step of the secant method on $|x|$ that does not land at the minimizer strictly decreases the function value and crosses zero.
-- source:
--   Lewis, Overton, Nonsmooth optimization via quasi-Newton methods, Math. Program. Ser. A 141 (2013) 135–163, pp. 151–152, §5.1, the sentence after the definition of A(t) and W(t)

import Mathlib
import Definitions.Def_NonsmoothQN_Secant_Basic
import Definitions.Def_NonsmoothQN_Secant_Expansion

namespace NonsmoothQN.Secant

theorem armijo_wolfe_sign_flip (x p t : ℝ) (hx : x ≠ 0) (hpx : p * x < 0)
    (hA : secA x p t) (hW : secW x p t) (hx' : x + t * p ≠ 0) :
    |x + t * p| < |x| ∧ x * (x + t * p) < 0 := by sorry

end NonsmoothQN.Secant
