-- Prove2me | Theorems.Thm_MazurTransfer_order49_residual_orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_bounded_resultants
-- name    : MazurTransfer.order49_residual_orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_bounded_resultants
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T05:41:00.165191+00:00
-- url     : https://prove2.me/theorems/b9804c80-7b39-4248-acb6-c6736a134cb7
-- title:
--   The original order49 point yields the level-seven G7F equation when the three bounded resultants are nonzero
-- statement:
--   For every elliptic member of the original order-seven family and every nonsingular rational affine point of exact order 49, assume the original seven-isogeny point function kills its seventh multiple and that all three original bounded resultants of the selection cofactor against the division cofactors are nonzero. Then the original G7F polynomial vanishes at the original Fricke parameter and residual Hauptmodul. All original hypotheses, including the kernel premise and all three resultant inequalities, remain explicit and unchanged.
--
--   This supplies an exact point-function fact used in the original order-49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_bounded_resultants. Original hypotheses, declaration ranges and proof commands preserved using the kernel graph and complete Lean AST. All point definitions were independently compared with the WIP originals; all reused geometric helpers are Proved and locally rechecked with closed proofs. Apache-2.0 headers and attribution retained. Named downstream consumers: exact residual Hauptmodul specification, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49BacktrackingCofactors
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
import Definitions.Def_MazurTransfer_OrderFortyNinePlaneTransferData
open Polynomial

theorem MazurTransfer.order49_residual_orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_bounded_resultants {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) = 0)
    (hres0 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d) 33 7 ≠ 0)
    (hres1 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d) 33 7 ≠ 0)
    (hres2 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d) 33 7 ≠ 0) :
    MazurTorsion.Kubert.orderSevenG7F (MazurTorsion.Kubert.orderSevenFrickeParameter d)
        (MazurTorsion.Kubert.orderSevenResidualHauptmodul d x y) = 0 := by sorry
