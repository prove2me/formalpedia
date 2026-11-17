-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_intrinsic_point_elimination
-- name    : HodgeComputer.FourPlusTwoResidual.intrinsic_point_elimination
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-16T06:54:21.061204+00:00
-- url     : https://prove2.me/theorems/60953e2d-0022-4ebf-b197-85070325197e
-- title:
--   Intrinsic point elimination for the 26-equation four-plus-two contact curve
-- statement:
--   Over any field $K$, consider the intrinsic moving-point equations
--
--   $$g_1 = L + Q\alpha^2, \qquad g_2 = (A_0 + A_1\alpha^2) + \alpha(B_0 + B_1\alpha^2),$$
--
--   together with the eliminated resultant $U_* = Q A_0 - L A_1$, $V_* = Q B_0 - L B_1$, and $H = Q U_*^2 + L V_*^2$. Assume $Q V_* \neq 0$. Then
--
--   $$(g_1 = 0 \land g_2 = 0) \iff (H = 0 \land \alpha = -U_*/V_*).$$
-- source:
--   Hodge Computer discussion #120 (four-plus-two-current/algebra/norm_system_circuit.json); FourPlusTwoIntrinsicElimination.lean

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem HodgeComputer.FourPlusTwoResidual.intrinsic_point_elimination
    {K : Type*} [Field K]
    (L Q A0 A1 B0 B1 alpha : K)
    (hQV : Q * (Q * B0 - L * B1) ≠ 0) :
    let U := Q * A0 - L * A1
    let V := Q * B0 - L * B1
    let H := Q * U ^ 2 + L * V ^ 2
    let g1 := L + Q * alpha ^ 2
    let g2 := A0 + A1 * alpha ^ 2 + alpha * (B0 + B1 * alpha ^ 2)
    (g1 = 0 ∧ g2 = 0) ↔ (H = 0 ∧ alpha = -U / V) := by sorry
