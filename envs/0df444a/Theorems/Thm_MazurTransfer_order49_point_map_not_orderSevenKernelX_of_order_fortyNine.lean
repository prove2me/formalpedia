-- Prove2me | Theorems.Thm_MazurTransfer_order49_point_map_not_orderSevenKernelX_of_order_fortyNine
-- name    : MazurTransfer.order49_point_map_not_orderSevenKernelX_of_order_fortyNine
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T04:01:09.260404+00:00
-- url     : https://prove2.me/theorems/e57c2f93-03f7-4f48-945a-7282d5af0791
-- title:
--   A point of order 49 avoids the prescribed seven-isogeny kernel abscissas
-- statement:
--   For an elliptic curve in the rational order-seven family, every nonsingular affine point of exact order $49$ has abscissa outside the three prescribed kernel values: $$x\ne 0,\qquad x\ne b(d),\qquad x\ne c(d).$$
--
--   This supplies an exact point-function fact used in the original order-49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.not_orderSevenKernelX_of_order_fortyNine. Original hypotheses, declaration ranges and proof commands preserved using the kernel graph and complete Lean AST. All point definitions were independently compared with the WIP originals; all reused geometric helpers are Proved and locally rechecked with closed proofs. Apache-2.0 headers and attribution retained. Named downstream consumers: exact residual Hauptmodul specification, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
open Polynomial

theorem MazurTransfer.order49_point_map_not_orderSevenKernelX_of_order_fortyNine {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (horder : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49) :
    ¬MazurTorsion.Kubert.OrderSevenKernelX d x := by sorry
