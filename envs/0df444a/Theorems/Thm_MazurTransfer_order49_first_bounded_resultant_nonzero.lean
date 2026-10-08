-- Prove2me | Theorems.Thm_MazurTransfer_order49_first_bounded_resultant_nonzero
-- name    : MazurTransfer.order49_first_bounded_resultant_nonzero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T21:56:11.703978+00:00
-- url     : https://prove2.me/theorems/ec413cf6-443a-4823-aa99-a00d680b5c17
-- title:
--   Order-49 first bounded resultant is nonzero at every nonsingular parameter
-- statement:
--   Let $G_d,H_{0,d}\in\mathbb Q[X]$ be the fixed selection and first division cofactors specialized at $d\in\mathbb Q$. If $d\ne0$, $d\ne1$ and $d^3-8d^2+5d+1\ne0$, then $$\operatorname{Res}_{33,7}(G_d,H_{0,d})\ne0.$$ This bounded-resultant statement allows the selection polynomial to lose degree at specialization and supplies the first algebraic obstruction used in the order-$49$ argument.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0 original headers retained. Exact original MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selection_divisionCofactor0_resultant_ne_zero statement and checked original helper proofs retained at complete original Lean AST command boundaries. No assumptions or coefficient data altered. Named downstream consumers: bounded_resultants_ne_zero and the full arbitrary-E order49 exclusion.

import Definitions.Def_MazurTransfer_Order49BacktrackingCofactors
import Definitions.Def_MazurTransfer_Order49ResultantFactorData
import Mathlib.RingTheory.Polynomial.Resultant.Basic

theorem MazurTransfer.order49_first_bounded_resultant_nonzero
    (d : ℚ) (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hcubic : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0) :
    Polynomial.resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d) 33 7 ≠ 0 := by sorry
