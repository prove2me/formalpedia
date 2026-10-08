-- Prove2me | Theorems.Thm_MazurTransfer_order49_doubling_geometry_orderSeven_kernel_double_certificate
-- name    : MazurTransfer.order49_doubling_geometry_orderSeven_kernel_double_certificate
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T03:50:09.775697+00:00
-- url     : https://prove2.me/theorems/01611578-c225-4bc6-907c-2fcd1567713f
-- title:
--   Exact kernel identity at homogeneous doubling coordinates
-- statement:
--   For $d,x\in\mathbb Q$, let $H$ be the original completed cubic of the source curve at $x$, and $p$ its original doubling abscissa numerator. With the prescribed family parameters $b(d),c(d)$, kernel polynomial $K_d$ and differential numerator $N_d$, $$p\bigl(p-b(d)H\bigr)\bigl(p-c(d)H\bigr)=K_d(x)N_d(x).$$ All coefficients and normalizations are those of the original rational order-seven family.
--
--   This exact certificate supports the original point-map doubling compatibility, then the exclusion of rational points of order $49$.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original _private.MazurTorsion.Kubert.OrderSevenIsogenyDoubling.0.MazurTorsion.Kubert.orderSeven_kernel_double_certificate. Every original hypothesis and proof command preserved at complete original Lean AST declaration ranges. Thirty-one algebraic formula values, including private originals, were compared directly against original kernel constants by kernel-checked reflexivity. Uses the Proved original homogeneous polynomial aggregate and exact separately registered doubling helper contracts. Apache-2.0 headers and attribution retained. Named downstream consumers: original coordinate and point-map doubling compatibility, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49DoublingCoordinateFormulas
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
open Polynomial

theorem MazurTransfer.order49_doubling_geometry_orderSeven_kernel_double_certificate (d x : ℚ) :
    let H := MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x
    let p := MazurTorsion.Doubling.xNumerator (MazurTorsion.Kubert.orderSevenFamily d) x
    p * (p - MazurTorsion.Kubert.orderSevenB d * H) * (p - MazurTorsion.Kubert.orderSevenC d * H) =
      MazurTorsion.Kubert.orderSevenKernelPolynomial d x *
        MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator d x := by sorry
