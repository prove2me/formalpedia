-- Prove2me | Theorems.Thm_MazurTransfer_order49_residual_polynomial_eval_obstruction_of_bounded_resultants
-- name    : MazurTransfer.order49_residual_polynomial_eval_obstruction_of_bounded_resultants
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T06:00:49.749414+00:00
-- url     : https://prove2.me/theorems/1a9abbcd-ac5c-4d16-9df1-f4f0c4f7a7f1
-- title:
--   Three nonzero bounded resultants exclude a common rational root of the selection polynomial and seventh division polynomial
-- statement:
--   For every elliptic member of the original order-seven family and every rational abscissa z, assume all three original bounded resultants of the selection and division cofactors are nonzero. Then the original selection polynomial does not vanish at z or the seventh division polynomial of the original quotient curve does not vanish there. All original hypotheses, including all three resultant inequalities, remain explicit.
--
--   This supplies an exact point-function fact used in the original order-49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.polynomial_eval_obstruction_of_bounded_resultants. Original hypotheses, declaration ranges and proof commands preserved using the kernel graph and complete Lean AST. All point definitions were independently compared with the WIP originals; all reused geometric helpers are Proved and locally rechecked with closed proofs. Apache-2.0 headers and attribution retained. Named downstream consumers: exact residual Hauptmodul specification, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49BacktrackingCofactors
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
open Polynomial

theorem MazurTransfer.order49_residual_polynomial_eval_obstruction_of_bounded_resultants (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hres0 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d) 33 7 ≠ 0)
    (hres1 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d) 33 7 ≠ 0)
    (hres2 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d) 33 7 ≠ 0)
    (z : ℚ) :
    MazurTorsion.Kubert.orderSevenSelectionPolynomial d z ≠ 0 ∨
      ((MazurTorsion.Kubert.orderSevenQuotient d).preΨ' 7).eval z ≠ 0 := by sorry
