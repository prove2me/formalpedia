-- Prove2me | Theorems.Thm_MazurTransfer_order49_point_map_orderSevenOrigin_nonsingular
-- name    : MazurTransfer.order49_point_map_orderSevenOrigin_nonsingular
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T03:32:06.469756+00:00
-- url     : https://prove2.me/theorems/d0eb9f98-23fe-4bdc-8078-0acd3928679e
-- title:
--   Nonsingularity of the marked origin of the rational order-seven family
-- statement:
--   Let $d \in\mathbb Q$ and assume the prescribed source curve is elliptic. Then the marked affine point $(0,0)$ is nonsingular on that curve. This fact supplies the proof-bearing constructor for the original marked point in the order-seven family.
--
--   This supplies an exact point-function fact used in the original order-49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.orderSevenOrigin_nonsingular. Original hypotheses, declaration ranges and proof commands preserved using the kernel graph and complete Lean AST. All point definitions were independently compared with the WIP originals; all reused geometric helpers are Proved and locally rechecked with closed proofs. Apache-2.0 headers and attribution retained. Named downstream consumers: exact residual Hauptmodul specification, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
open Polynomial

theorem MazurTransfer.order49_point_map_orderSevenOrigin_nonsingular (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular 0 0 := by sorry
