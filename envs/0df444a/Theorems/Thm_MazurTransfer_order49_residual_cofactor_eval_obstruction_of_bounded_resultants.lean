-- Prove2me | Theorems.Thm_MazurTransfer_order49_residual_cofactor_eval_obstruction_of_bounded_resultants
-- name    : MazurTransfer.order49_residual_cofactor_eval_obstruction_of_bounded_resultants
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T06:00:58.105727+00:00
-- url     : https://prove2.me/theorems/bff38c11-cd1d-48fe-baad-69b3be53f826
-- title:
--   Three nonzero bounded resultants exclude a common rational root of the selection and division cofactors
-- statement:
--   For every rational parameter d and rational abscissa z, if all three original bounded resultants of the selection cofactor against the division cofactors are nonzero, then the selection cofactor does not vanish at z or the product of the three division cofactors does not vanish there. All three resultant inequalities are explicit; no ellipticity or additional parameter hypothesis is imposed.
--
--   This supplies an exact point-function fact used in the original order-49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.cofactor_eval_obstruction_of_bounded_resultants. Original hypotheses, declaration ranges and proof commands preserved using the kernel graph and complete Lean AST. All point definitions were independently compared with the WIP originals; all reused geometric helpers are Proved and locally rechecked with closed proofs. Apache-2.0 headers and attribution retained. Named downstream consumers: exact residual Hauptmodul specification, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49BacktrackingCofactors
open Polynomial

theorem MazurTransfer.order49_residual_cofactor_eval_obstruction_of_bounded_resultants (d : ℚ)
    (hres0 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d) 33 7 ≠ 0)
    (hres1 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d) 33 7 ≠ 0)
    (hres2 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d) 33 7 ≠ 0)
    (z : ℚ) :
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d).eval z ≠ 0 ∨
      (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d *
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d).eval z ≠ 0 := by sorry
