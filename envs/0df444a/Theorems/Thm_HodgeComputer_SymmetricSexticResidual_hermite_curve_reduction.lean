-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_hermite_curve_reduction
-- name    : HodgeComputer.SymmetricSexticResidual.hermite_curve_reduction
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-16T05:48:23.890883+00:00
-- url     : https://prove2.me/theorems/8ce31985-607d-4b47-bce7-68fd85fdee08
-- title:
--   Symmetric sextic: Hermite reduction on the square-coordinate curve
-- statement:
--   Let $K$ be a field of characteristic zero with a derivation $D : K \to K$ representing differentiation in $x$ along a plane curve $f(x, u) = 0$. Write $g = f_u$, $n = f_x$, $g_u = f_{uu}$, $\nu = f_{xu}$, $n_n = f_{xx}$, and suppose $x, g, n \neq 0$ and the implicit chain rules $D(Q) = Q_x - (n/g) Q_u$, $D(n) = n_n - (n/g) \nu$, and $D(g) = \nu - (n/g) g_u$ hold. Then
--
--   $$\frac{g Q_u - g_u Q}{g^3} = \left(D\!\left(-\frac{Q}{n g}\right) + \frac{-Q / (n g)}{2 x}\right) + \frac{2 x (Q_x n - Q n_n) + Q n}{2 x n^2 g}.$$
--
--   This Hermite identity reduces the cubic pole order in $g = f_u$ to a simple pole in $g$ at the cost of a quadratic pole in $n = f_x$.
-- source:
--   https://github.com/hodge-computer/sextics/discussions/117#discussioncomment-19498520 (symmetric-contact-current/source/lean/SymmetricRatioCurrent.lean, HermiteIdentity.reduce_scaled)

import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem HodgeComputer.SymmetricSexticResidual.hermite_curve_reduction
    {K : Type*} [Field K] [CharZero K]
    (D : Derivation ℤ K K)
    (x g n gu nu nn Q Qx Qu : K)
    (hx : x ≠ 0) (hg : g ≠ 0) (hn : n ≠ 0)
    (hQ : D Q = Qx - n * Qu / g)
    (hnD : D n = nn - n * nu / g)
    (hgD : D g = nu - n * gu / g) :
    (g * Qu - gu * Q) / g ^ 3 =
      (D (-Q / (n * g)) + (-Q / (n * g)) / (2 * x)) +
        ((2 * x * (Qx * n - Q * nn) + Q * n) / (n ^ 2 * g)) / (2 * x) := by sorry
