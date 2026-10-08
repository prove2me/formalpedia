-- Prove2me | Theorems.Thm_HessianDamping_IPAHDSC_term1_nonneg
-- name    : HessianDamping.IPAHDSC.term1_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:36.530974+00:00
-- url     : https://prove2.me/theorems/4f529641-be03-4103-b864-003c3e389654
-- title:
--   Term 1, proof of Theorem 9, p. 25 — (√µ µ/4)X² + (β/2)Y² − βµXY ≥ 0 for 0 ≤ β ≤ 1/(2√µ)
-- statement:
--   Let $\mu>0$ and $0\le\beta\le\frac{1}{2\sqrt\mu}$. Then for all real numbers $X,Y$,
--   $$\frac{\sqrt\mu\,\mu}{4}X^2+\frac\beta2Y^2-\beta\mu XY\ge0.$$
--
--   In the proof of Theorem 9 this is applied with $X=\|x_{k+1}-x^\star\|$ and $Y=\|\nabla f(x_{k+1})\|$ to show that the first group of remainder terms in the energy estimate is nonnegative.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 25, proof of Theorem 9, Term 1

import Mathlib
import Definitions.Def_HessianDamping_IPAHDSC_Setting

namespace HessianDamping.IPAHDSC

/-- Term 1, proof of Theorem 9, p. 25: for `0 ≤ β ≤ 1/(2√μ)`,
`(√μ μ/4) X² + (β/2) Y² - βμ X Y ≥ 0` for all reals `X`, `Y`. -/
theorem term1_nonneg (μ β : ℝ) (hμ : 0 < μ) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / (2 * Real.sqrt μ))
    (X Y : ℝ) :
    0 ≤ Real.sqrt μ * μ / 4 * X ^ 2 + β / 2 * Y ^ 2 - β * μ * X * Y := by sorry

end HessianDamping.IPAHDSC
