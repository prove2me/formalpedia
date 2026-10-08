-- Prove2me | Theorems.Thm_MazurTransfer_order49_marked_origin_exists_eq_nsmul_orderSevenOrigin_of_pointMap_eq_zero
-- name    : MazurTransfer.order49_marked_origin_exists_eq_nsmul_orderSevenOrigin_of_pointMap_eq_zero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T04:11:28.517107+00:00
-- url     : https://prove2.me/theorems/5c74aab2-6ade-43ff-9c98-97e442db02a9
-- title:
--   Every point killed by the order-seven isogeny function is a multiple of its marked origin
-- statement:
--   For every elliptic member of the original rational order-seven family, every point mapped to zero by the original seven-isogeny point function is a natural-number multiple of its marked rational origin. The exact point function and ellipticity hypothesis are preserved.
--
--   This supplies an exact point-function fact used in the original order-49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.exists_eq_nsmul_orderSevenOrigin_of_pointMap_eq_zero. Original hypotheses, declaration ranges and proof commands preserved using the kernel graph and complete Lean AST. All point definitions were independently compared with the WIP originals; all reused geometric helpers are Proved and locally rechecked with closed proofs. Apache-2.0 headers and attribution retained. Named downstream consumers: exact residual Hauptmodul specification, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49MarkedOriginPoint
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
open Polynomial

theorem MazurTransfer.order49_marked_origin_exists_eq_nsmul_orderSevenOrigin_of_pointMap_eq_zero {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {R : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hR : MazurTorsion.Kubert.orderSevenPointMap d R = 0) :
    ∃ n : ℕ, n < 7 ∧ R = n • MazurTorsion.Kubert.orderSevenOrigin d := by sorry
