-- Prove2me | Theorems.Thm_MazurTransfer_x0_49_rational_points_two_cusps
-- name    : MazurTransfer.x0_49_rational_points_two_cusps
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T14:44:56.001489+00:00
-- url     : https://prove2.me/theorems/f8534410-433f-40e6-951c-448d9f701ebe
-- title:
--   Rational points on the order-49 model: two-cusps
-- statement:
--   Every rational point on $E_{49}:y^2=x(x^2+21x+112)$ is either the point at infinity or $T=(0,0)$. Equivalently, $E_{49}(\mathbb Q)=\{O,T\}$. The downstream explicit level-seven correspondence transfer sends a hypothetical noncuspidal solution to an affine point with nonzero abscissa and obtains a contradiction. The correspondence construction and its relation to arbitrary order-49 torsion remain separate obligations.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: XZeroFortyNineDescent.lean and XZeroFortyNineReduction.lean. Exact original arithmetic conclusion, with the concrete good-reduction count supplied by the Proved full rational torsion interface. Original Apache-2.0 headers retained.

import Definitions.Def_MazurTransfer_XZeroFortyNineCurveData

theorem MazurTransfer.x0_49_rational_points_two_cusps :
  ∀ P : MazurTorsion.XZeroFortyNine.curve.toAffine.Point,
    P = 0 ∨ P = MazurTorsion.XZeroFortyNine.T := by sorry
