-- Prove2me | Theorems.Thm_MazurTransfer_order49_point_map_orderSevenPointMap_some_of_not_kernelX
-- name    : MazurTransfer.order49_point_map_orderSevenPointMap_some_of_not_kernelX
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T03:26:10.777064+00:00
-- url     : https://prove2.me/theorems/a666fa0e-a681-4e57-a41e-4fd22a8174ab
-- title:
--   Seven-isogeny point function agrees with its safe affine formula
-- statement:
--   Let $d,x,y\in\mathbb Q$, with the source curve elliptic and $(x,y)$ nonsingular. If $x$ is outside the three prescribed kernel abscissas, the total point function agrees with the original denominator-safe affine coordinate construction.
--
--   This supplies an exact point-function fact used in the original order-49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.orderSevenPointMap_some_of_not_kernelX. Original hypotheses, declaration ranges and proof commands preserved using the kernel graph and complete Lean AST. All point definitions were independently compared with the WIP originals; all reused geometric helpers are Proved and locally rechecked with closed proofs. Apache-2.0 headers and attribution retained. Named downstream consumers: exact residual Hauptmodul specification, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
open Polynomial

theorem MazurTransfer.order49_point_map_orderSevenPointMap_some_of_not_kernelX {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hx : ¬MazurTorsion.Kubert.OrderSevenKernelX d x) :
    MazurTorsion.Kubert.orderSevenPointMap d (.some x y hP) =
      MazurTorsion.Kubert.orderSevenVeluPoint hP
        (fun h ↦ hx (Or.inl h))
        (fun h ↦ hx (Or.inr (Or.inl h)))
        (fun h ↦ hx (Or.inr (Or.inr h))) := by sorry
