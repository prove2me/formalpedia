-- Prove2me | Theorems.Thm_MazurTransfer_order49_coordinate_orderSevenVelu_double_coordinates
-- name    : MazurTransfer.order49_coordinate_orderSevenVelu_double_coordinates
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T04:14:30.666641+00:00
-- url     : https://prove2.me/theorems/453022e0-6b73-4245-ad74-d8c04c885b8a
-- title:
--   Exact coordinates for doubling the order-seven isogeny at a point of order 49
-- statement:
--   For every nonsingular rational point of exact order 49 on an elliptic member of the original order-seven family, the original full abscissa and completed-ordinate doubling-coordinate certificate holds. Every parameter, coordinate and ellipticity hypothesis is preserved.
--
--   This supplies an exact point-function fact used in the original order-49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original _private.MazurTorsion.Kubert.OrderSevenIsogenyDoubling.0.MazurTorsion.Kubert.orderSevenVelu_double_coordinates. Original hypotheses, declaration ranges and proof commands preserved using the kernel graph and complete Lean AST. All point definitions were independently compared with the WIP originals; all reused geometric helpers are Proved and locally rechecked with closed proofs. Apache-2.0 headers and attribution retained. Named downstream consumers: exact residual Hauptmodul specification, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49DoublingCoordinateFormulas
open Polynomial

theorem MazurTransfer.order49_coordinate_orderSevenVelu_double_coordinates {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (horder : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49) :
    MazurTorsion.Kubert.OrderSevenDoublingCoordinates d x y := by sorry
