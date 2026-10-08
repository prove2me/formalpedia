-- Prove2me | Theorems.Thm_HessianDamping_DINSC_quad_form_nonneg
-- name    : HessianDamping.DINSC.quad_form_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:04.066665+00:00
-- url     : https://prove2.me/theorems/74aef8ff-5a15-4a41-a092-4945e26579fc
-- title:
--   Proof of Theorem 7, p. 21 — (μ/4)X² + (β/(2√μ))Y² − β√μXY ≥ 0 when 0 ≤ β ≤ 1/(2√μ)
-- statement:
--   Let $\mu>0$ and $0\le\beta\le\frac{1}{2\sqrt\mu}$. Then for all real numbers $X,Y$,
--   $$\frac{\mu}{4}X^2+\frac{\beta}{2\sqrt\mu}Y^2-\beta\sqrt\mu\,XY\ \ge\ 0 .$$
--
--   In the proof of Theorem 7 it is applied with $X=\|x(t)-x^\star\|$ and $Y=\|\nabla f(x(t))\|$; it is where the upper bound $\beta\le 1/(2\sqrt\mu)$ is used.
--
--   **Formalization Note.** The page needs the inequality only for $X,Y\ge0$; it is stated for all real $X,Y$, where it is equally true.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 21, §4.1, proof of Theorem 7 (i), display after 'Elementary algebraic computation gives'

import Mathlib
import Definitions.Def_HessianDamping_DINSC_Setting

namespace HessianDamping.DINSC

open Set

/-- Proof of Theorem 7, p. 21: for `0 ≤ β ≤ 1/(2√μ)`, the quadratic form
`(μ/4)X² + (β/(2√μ))Y² − β√μ XY` is nonnegative. -/
theorem quad_form_nonneg (μ : ℝ) (hμ : 0 < μ) (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / (2 * Real.sqrt μ)) :
    ∀ X Y : ℝ, 0 ≤ μ / 4 * X ^ 2 + β / (2 * Real.sqrt μ) * Y ^ 2 - β * Real.sqrt μ * X * Y := by sorry

end HessianDamping.DINSC
