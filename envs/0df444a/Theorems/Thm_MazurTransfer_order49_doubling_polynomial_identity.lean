-- Prove2me | Theorems.Thm_MazurTransfer_order49_doubling_polynomial_identity
-- name    : MazurTransfer.order49_doubling_polynomial_identity
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T02:43:13.013059+00:00
-- url     : https://prove2.me/theorems/01df8b5d-9980-4eed-95b9-111d08381230
-- title:
--   Homogeneous doubling identity for the seven-isogeny
-- statement:
--   For every rational parameter $d$, the two original homogeneous polynomial expressions for doubling through the explicit order-seven isogeny agree as polynomials in the abscissa. Both sides have degree at most $28$.
--
--   This polynomial identity supports the full exclusion of rational points of order $49$ on elliptic curves over $\mathbb Q$.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.OrderSevenDoublingCertificate.polynomial_identity. Original signature and entire interpolation proof preserved at complete Lean AST source ranges, with exact original evaluation blocks as registered children. Apache-2.0 headers and attribution retained. Named downstream consumer: full every-curve order49 exclusion.

import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
open Polynomial

theorem MazurTransfer.order49_doubling_polynomial_identity (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXHomogeneousPolynomial d (MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceDoubleXPolynomial d)
        (MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceCompletedCubicPolynomial d) =
      MazurTorsion.Kubert.OrderSevenDoublingCertificate.doubleXHomogeneousPolynomial (MazurTorsion.Kubert.orderSevenQuotient d)
        (MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXPolynomial d) (MazurTorsion.Kubert.OrderSevenDoublingCertificate.kernelPolynomial d ^ 2) := by sorry
