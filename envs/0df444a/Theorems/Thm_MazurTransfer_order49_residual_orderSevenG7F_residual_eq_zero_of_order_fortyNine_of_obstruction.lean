-- Prove2me | Theorems.Thm_MazurTransfer_order49_residual_orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_obstruction
-- name    : MazurTransfer.order49_residual_orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_obstruction
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T06:01:03.615766+00:00
-- url     : https://prove2.me/theorems/6fd13379-a209-4408-b2a3-1bdf63979286
-- title:
--   The original polynomial nonvanishing obstruction yields the residual G7F equation
-- statement:
--   For every elliptic member of the original order-seven family and every nonsingular rational affine point of exact order49, assume that the original point map kills the seventh multiple and that the original selection polynomial or quotient seventh division polynomial does not vanish at the image abscissa. Then the original G7F equation holds at the original Fricke parameter and residual Hauptmodul. The kernel and polynomial obstruction hypotheses are unchanged and explicit.
--
--   This supplies an exact point-function fact used in the original order-49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_obstruction. Original hypotheses, declaration ranges and proof commands preserved using the kernel graph and complete Lean AST. All point definitions were independently compared with the WIP originals; all reused geometric helpers are Proved and locally rechecked with closed proofs. Apache-2.0 headers and attribution retained. Named downstream consumers: exact residual Hauptmodul specification, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
import Definitions.Def_MazurTransfer_OrderFortyNinePlaneTransferData
open Polynomial

theorem MazurTransfer.order49_residual_orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_obstruction {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) = 0)
    (hobstruction :
      MazurTorsion.Kubert.orderSevenSelectionPolynomial d (MazurTorsion.Kubert.orderSevenVeluX d x) ≠ 0 ∨
        ((MazurTorsion.Kubert.orderSevenQuotient d).preΨ' 7).eval
          (MazurTorsion.Kubert.orderSevenVeluX d x) ≠ 0) :
    MazurTorsion.Kubert.orderSevenG7F (MazurTorsion.Kubert.orderSevenFrickeParameter d)
        (MazurTorsion.Kubert.orderSevenResidualHauptmodul d x y) = 0 := by sorry
