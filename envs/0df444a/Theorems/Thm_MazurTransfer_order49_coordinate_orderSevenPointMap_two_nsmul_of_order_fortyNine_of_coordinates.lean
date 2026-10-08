-- Prove2me | Theorems.Thm_MazurTransfer_order49_coordinate_orderSevenPointMap_two_nsmul_of_order_fortyNine_of_coordinates
-- name    : MazurTransfer.order49_coordinate_orderSevenPointMap_two_nsmul_of_order_fortyNine_of_coordinates
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T04:13:22.195069+00:00
-- url     : https://prove2.me/theorems/c5f51acd-0904-4c00-a02e-b0244a959785
-- title:
--   The seven-isogeny point function respects doubling when its coordinate certificate holds
-- statement:
--   For every elliptic member of the original order-seven family and every point of exact order 49, the original point function respects doubling provided the full original coordinate certificate holds at every affine point of order 49. The coordinate assumption is explicit and will be discharged by the separately proved exact coordinate theorem.
--
--   This supplies an exact point-function fact used in the original order-49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original _private.MazurTorsion.Kubert.OrderSevenIsogenyDoubling.0.MazurTorsion.Kubert.orderSevenPointMap_two_nsmul_of_order_fortyNine_of_coordinates. Original hypotheses, declaration ranges and proof commands preserved using the kernel graph and complete Lean AST. All point definitions were independently compared with the WIP originals; all reused geometric helpers are Proved and locally rechecked with closed proofs. Apache-2.0 headers and attribution retained. Named downstream consumers: exact residual Hauptmodul specification, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49DoublingCoordinateFormulas
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
open Polynomial

theorem MazurTransfer.order49_coordinate_orderSevenPointMap_two_nsmul_of_order_fortyNine_of_coordinates {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hcoordinates : ∀ {x y : ℚ}
      (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y),
      addOrderOf
          (WeierstrassCurve.Affine.Point.some x y hP :
            (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49 →
        MazurTorsion.Kubert.OrderSevenDoublingCoordinates d x y)
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49) :
    MazurTorsion.Kubert.orderSevenPointMap d ((2 : ℕ) • Q) =
      (2 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q := by sorry
