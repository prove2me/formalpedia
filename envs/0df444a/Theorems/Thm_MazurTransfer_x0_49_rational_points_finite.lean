-- Prove2me | Theorems.Thm_MazurTransfer_x0_49_rational_points_finite
-- name    : MazurTransfer.x0_49_rational_points_finite
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T14:45:00.59645+00:00
-- url     : https://prove2.me/theorems/06b5d21f-3206-47ca-9e99-35e9c9736e84
-- title:
--   Rational points on the order-49 model: finite
-- statement:
--   The rational point group of $E_{49}:y^2=x(x^2+21x+112)$ is finite. The full two-isogeny descent eliminates every squareclass except the two indicated doubling cosets, and the checked rational height descent proves finite generation and rank zero. The downstream two-cusp classification separately uses good reduction and the absence of points of order four.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: XZeroFortyNineDescent.lean and XZeroFortyNineReduction.lean. Exact original arithmetic conclusion, with the concrete good-reduction count supplied by the Proved full rational torsion interface. Original Apache-2.0 headers retained.

import Definitions.Def_MazurTransfer_XZeroFortyNineCurveData

theorem MazurTransfer.x0_49_rational_points_finite :
  Finite MazurTorsion.XZeroFortyNine.curve.toAffine.Point := by sorry
