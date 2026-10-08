-- Prove2me | Theorems.Thm_MazurTransfer_order49_translation_orderSevenVeluPoint_add_origin
-- name    : MazurTransfer.order49_translation_orderSevenVeluPoint_add_origin
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T04:54:20.099318+00:00
-- url     : https://prove2.me/theorems/6437c5c6-c3e2-4226-9234-3b55f467db5a
-- title:
--   The original seven-isogeny affine point is unchanged by marked-origin translation
-- statement:
--   The exact original affine translation identity, with both nonsingular affine points, their marked-origin addition relation, ellipticity and all six original kernel-abscissa exclusions retained.
--
--   This supplies an exact point-function fact used in the original order-49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.orderSevenVeluPoint_add_origin. Original hypotheses, declaration ranges and proof commands preserved using the kernel graph and complete Lean AST. All point definitions were independently compared with the WIP originals; all reused geometric helpers are Proved and locally rechecked with closed proofs. Apache-2.0 headers and attribution retained. Named downstream consumers: exact residual Hauptmodul specification, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49MarkedOriginPoint
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
open Polynomial

theorem MazurTransfer.order49_translation_orderSevenVeluPoint_add_origin {d x y x' y' : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hP' : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x' y')
    (hadd :
      (WeierstrassCurve.Affine.Point.some x y hP :
          (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) + MazurTorsion.Kubert.orderSevenOrigin d =
        WeierstrassCurve.Affine.Point.some x' y' hP')
    (hx0 : x ≠ 0) (hxb : x ≠ MazurTorsion.Kubert.orderSevenB d)
    (hxc : x ≠ MazurTorsion.Kubert.orderSevenC d)
    (hx0' : x' ≠ 0) (hxb' : x' ≠ MazurTorsion.Kubert.orderSevenB d)
    (hxc' : x' ≠ MazurTorsion.Kubert.orderSevenC d) :
    MazurTorsion.Kubert.orderSevenVeluPoint hP' hx0' hxb' hxc' =
      MazurTorsion.Kubert.orderSevenVeluPoint hP hx0 hxb hxc := by sorry
