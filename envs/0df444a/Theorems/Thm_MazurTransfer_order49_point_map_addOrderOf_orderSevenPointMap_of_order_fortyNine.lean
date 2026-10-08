-- Prove2me | Theorems.Thm_MazurTransfer_order49_point_map_addOrderOf_orderSevenPointMap_of_order_fortyNine
-- name    : MazurTransfer.order49_point_map_addOrderOf_orderSevenPointMap_of_order_fortyNine
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T03:31:06.459081+00:00
-- url     : https://prove2.me/theorems/b12dc0e0-d405-4607-8211-42f265fd64d2
-- title:
--   Order of the seven-isogeny image under explicit seventh-multiple hypotheses
-- statement:
--   For an elliptic source curve in the rational order-seven family, let $Q$ be a rational point of exact order $49$, and let $\phi_d$ be the original explicit point function. Assume both $$\phi_d(7Q)=0,\qquad \phi_d(7Q)=7\phi_d(Q).$$ Then $$\operatorname{ord}(\phi_d(Q))=7.$$ Both seventh-multiple assumptions are explicit; this contract alone does not assert that the point function is a group homomorphism. The downstream original order-of-image consumer establishes the required compatibility separately.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.addOrderOf_orderSevenPointMap_of_order_fortyNine. Complete original Lean AST signature and proof commands preserved, including both seventh-multiple hypotheses. Uses the exact registered kernel-killed-by-seven child. Apache-2.0 headers and attribution retained. Named downstream consumers: original addOrderOf_orderSevenPointMap_of_order_fortyNine_of_kernel, residual Hauptmodul specification, and full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
open Polynomial

theorem MazurTransfer.order49_point_map_addOrderOf_orderSevenPointMap_of_order_fortyNine {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d ((7 : ℕ) • Q) = 0)
    (hmap : MazurTorsion.Kubert.orderSevenPointMap d ((7 : ℕ) • Q) =
      (7 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q) :
    addOrderOf (MazurTorsion.Kubert.orderSevenPointMap d Q) = 7 := by sorry
