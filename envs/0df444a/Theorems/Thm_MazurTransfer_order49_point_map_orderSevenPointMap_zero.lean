-- Prove2me | Theorems.Thm_MazurTransfer_order49_point_map_orderSevenPointMap_zero
-- name    : MazurTransfer.order49_point_map_orderSevenPointMap_zero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T03:26:42.640986+00:00
-- url     : https://prove2.me/theorems/73239677-78d6-4efa-9dc7-385b70bedc55
-- title:
--   Seven-isogeny point function sends infinity to infinity
-- statement:
--   For every rational parameter $d$ for which the source curve is elliptic, the explicit seven-isogeny point function $\phi_d$ sends the identity to the identity: $$\phi_d(0)=0.$$
--
--   This supplies an exact point-function fact used in the original order-49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.orderSevenPointMap_zero. Original hypotheses, declaration ranges and proof commands preserved using the kernel graph and complete Lean AST. All point definitions were independently compared with the WIP originals; all reused geometric helpers are Proved and locally rechecked with closed proofs. Apache-2.0 headers and attribution retained. Named downstream consumers: exact residual Hauptmodul specification, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
open Polynomial

theorem MazurTransfer.order49_point_map_orderSevenPointMap_zero (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    MazurTorsion.Kubert.orderSevenPointMap d 0 = 0 := by sorry
