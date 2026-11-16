-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_intrinsic_point_elimination
-- name    : HodgeComputer.SymmetricSexticResidual.intrinsic_point_elimination
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-16T05:48:24.04989+00:00
-- url     : https://prove2.me/theorems/7c023425-751b-4728-8ffa-c4efc3df256d
-- title:
--   Symmetric sextic: 26-equation intrinsic moving-point elimination
-- statement:
--   In the intrinsic contact chart for the symmetric sextic, eliminating the normal coordinate via the monic quadric reduces the moving-point equations to $g_1 = L + Q \alpha^2 = 0$ and $g_2 = A_0 + A_1 \alpha^2 + \alpha(B_0 + B_1 \alpha^2) = 0$. Define $U = Q A_0 - L A_1$, $V = Q B_0 - L B_1$, and the resultant polynomial $H = Q U^2 + L V^2$. Then:
--
--   1. $Q g_2 - (A_1 + \alpha B_1) g_1 = U + \alpha V$ and $H = Q(U + \alpha V)(U - \alpha V) + g_1 V^2$.
--
--   2. On the open locus $Q \neq 0$ and $V \neq 0$, the system $g_1 = g_2 = 0$ is equivalent to $H = 0$ and $\alpha = -U / V$.
--
--   3. Along $g_1 = g_2 = 0$, any first-order parameter variation $\dot{(\cdot)}$ (holding the base coordinates fixed) satisfies the exact Jacobian transformation
--
--   $$\dot H = Q V \left(\dot g_1 \frac{\partial g_2}{\partial \alpha} - \frac{\partial g_1}{\partial \alpha} \dot g_2\right).$$
--
--   This reduces the 27-variable moving-point system to 26 equations in the 26 contact coordinates.
-- source:
--   https://github.com/hodge-computer/sextics/discussions/117#discussioncomment-19498520 (symmetric-contact-current/contact/symmetric/ADJUNCTION_RESIDUE_ROUTE.md §6)

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem HodgeComputer.SymmetricSexticResidual.intrinsic_point_elimination
    (L Q A0 A1 B0 B1 alpha Ld Qd A0d A1d B0d B1d : ℂ) :
    let U := Q * A0 - L * A1
    let V := Q * B0 - L * B1
    let H := Q * U ^ 2 + L * V ^ 2
    let g1 := L + Q * alpha ^ 2
    let g2 := A0 + A1 * alpha ^ 2 + alpha * (B0 + B1 * alpha ^ 2)
    let dtau_g1 := Ld + Qd * alpha ^ 2
    let dalpha_g1 := 2 * Q * alpha
    let dtau_g2 := A0d + A1d * alpha ^ 2 + alpha * (B0d + B1d * alpha ^ 2)
    let dalpha_g2 := 2 * A1 * alpha + B0 + 3 * B1 * alpha ^ 2
    let dtau_U := Qd * A0 + Q * A0d - Ld * A1 - L * A1d
    let dtau_V := Qd * B0 + Q * B0d - Ld * B1 - L * B1d
    let dtau_H := Qd * U ^ 2 + 2 * Q * U * dtau_U + Ld * V ^ 2 + 2 * L * V * dtau_V
    (Q * g2 - (A1 + alpha * B1) * g1 = U + alpha * V) ∧
    (H = Q * (U + alpha * V) * (U - alpha * V) + g1 * V ^ 2) ∧
    (Q ≠ 0 → V ≠ 0 →
      ((g1 = 0 ∧ g2 = 0) ↔ (H = 0 ∧ alpha = -U / V))) ∧
    (g1 = 0 → g2 = 0 →
      dtau_H = Q * V * (dtau_g1 * dalpha_g2 - dalpha_g1 * dtau_g2)) := by sorry
