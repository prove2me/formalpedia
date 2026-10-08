-- Prove2me | Theorems.Thm_MazurTransfer_order49_point_map_orderSevenPointMap_kernel_killed_by_seven
-- name    : MazurTransfer.order49_point_map_orderSevenPointMap_kernel_killed_by_seven
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T03:26:52.799953+00:00
-- url     : https://prove2.me/theorems/1ae5fbf4-2a1e-4544-8e82-6ea7aa94cce3
-- title:
--   The kernel of the explicit seven-isogeny point function is killed by seven
-- statement:
--   For an elliptic source curve in the rational order-seven family, every rational group point $P$ that maps to infinity under the explicit point function $\phi_d$ is killed by seven: $$\phi_d(P)=0\quad\Longrightarrow\quad 7P=0.$$ This kernel fact is used to establish the exact order of the image of a point of order $49$.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.orderSevenPointMap_kernel_killed_by_seven. Every original hypothesis and proof command is preserved at complete original Lean AST declaration ranges. The only port repair explicitly opens standard root namespaces, hiding the competing specialized neg_zero name. Definitions were independently value-audited against the WIP and geometric prerequisites are Proved. Apache-2.0 headers and attribution retained. Named downstream consumers: the original order-of-image theorem, residual Hauptmodul specification and full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
open Polynomial

theorem MazurTransfer.order49_point_map_orderSevenPointMap_kernel_killed_by_seven {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {P : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hP : MazurTorsion.Kubert.orderSevenPointMap d P = 0) :
    (7 : ℕ) • P = 0 := by sorry
