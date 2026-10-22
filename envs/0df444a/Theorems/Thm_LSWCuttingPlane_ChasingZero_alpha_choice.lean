-- Prove2me | Theorems.Thm_LSWCuttingPlane_ChasingZero_alpha_choice
-- name    : LSWCuttingPlane.ChasingZero.alpha_choice
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T22:59:41.598525+00:00
-- url     : https://prove2.me/theorems/038e6289-affa-43d1-9d4a-2932ade3da14
-- title:
--   Proof of Theorem 34, p. 44 — with α = 1/(2(c+R)): e^{2α(c+R)}(α(c+R))² ≤ 1 and α²e^{αc}c² ≤ e^{−α(R+c)}
-- statement:
--   Let $c>0$ and $R>0$, and put $\alpha=\dfrac{1}{2(c+R)}$. Then
--   $$e^{2\alpha(c+R)}\big(\alpha(c+R)\big)^2\le1\qquad\text{and}\qquad \alpha^2e^{\alpha c}c^2\le e^{-\alpha(R+c)}.$$
--
--   This is the choice of the scale $\alpha$ of the exponential potential in the proof of Theorem 34: it makes the adversary's drift term $\alpha^2e^{\alpha c}c^2\eta$ no larger than the decrease $e^{-\alpha(R+c)}\eta$ claimed for the player's reset, and it fixes the factor $2(c+R)=1/\alpha$ in the final bound.
-- source:
--   Lee, Sidford, Wong, A Faster Cutting Plane Method and its Implications for Combinatorial and Convex Optimization, arXiv:1508.04874v2, p. 44, proof of Theorem 34, first sentence

import Mathlib
import Definitions.Def_LSWCuttingPlane_ChasingZero_Setting

namespace LSWCuttingPlane.ChasingZero

/-- Proof of Theorem 34, p. 44: with `α = 1/(2(c + R))`,
`e^{2α(c+R)} (α(c + R))² ≤ 1` and `α² e^{αc} c² ≤ e^{−α(R+c)}`. -/
theorem alpha_choice (c R α : ℝ) (hc : 0 < c) (hR : 0 < R) (hα : α = 1 / (2 * (c + R))) :
    Real.exp (2 * α * (c + R)) * (α * (c + R)) ^ 2 ≤ 1 ∧
      α ^ 2 * Real.exp (α * c) * c ^ 2 ≤ Real.exp (-(α * (R + c))) := by sorry

end LSWCuttingPlane.ChasingZero
