-- Prove2me | Theorems.Thm_MazurTransfer_order49_point_map_orderSevenPointMap_some_eq_zero_iff
-- name    : MazurTransfer.order49_point_map_orderSevenPointMap_some_eq_zero_iff
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T03:26:17.511014+00:00
-- url     : https://prove2.me/theorems/93fb46c0-bc02-4f19-b34b-6a46bbed2e9f
-- title:
--   Exact affine kernel of the seven-isogeny point function
-- statement:
--   Let $d,x,y\in\mathbb Q$, with the source curve elliptic and $(x,y)$ a nonsingular source point. The explicit point function sends this point to infinity exactly when its abscissa belongs to the prescribed kernel set: $$\phi_d(x,y)=0\quad\Longleftrightarrow\quad x=0\;\lor\;x=b(d)\;\lor\;x=c(d).$$ Here $b(d)$ and $c(d)$ are the original order-seven family parameters.
--
--   This supplies an exact point-function fact used in the original order-49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.orderSevenPointMap_some_eq_zero_iff. Original hypotheses, declaration ranges and proof commands preserved using the kernel graph and complete Lean AST. All point definitions were independently compared with the WIP originals; all reused geometric helpers are Proved and locally rechecked with closed proofs. Apache-2.0 headers and attribution retained. Named downstream consumers: exact residual Hauptmodul specification, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
open Polynomial

theorem MazurTransfer.order49_point_map_orderSevenPointMap_some_eq_zero_iff {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y) :
    MazurTorsion.Kubert.orderSevenPointMap d (.some x y hP) = 0 ↔
      MazurTorsion.Kubert.OrderSevenKernelX d x := by sorry
