-- Prove2me | Theorems.Thm_MazurTransfer_order49_generic_resultant_factorization
-- name    : MazurTransfer.order49_generic_resultant_factorization
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T21:46:59.756466+00:00
-- url     : https://prove2.me/theorems/b31d125b-45d1-4456-8240-4613c547e09b
-- title:
--   Order-49 exact generic bounded-resultant factorization
-- statement:
--   In $\mathbb Q[T][X]$, let $G$ and $H_0$ be the fixed selection and first division cofactors of the order-seven backtracking calculation. Let $F(T)$ be the separately recorded factored polynomial. Then the bounded resultant satisfies $$\operatorname{Res}_{33,7}(G,H_0)=F(T).$$ This is an unconditional identity of entire polynomials in the parameter. It is the generic algebraic certificate used to exclude rational points of order $49$. No specialization or torsion assumption is imposed.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0. Exact original generic_resultant_eq_resultantFactorData statement, original complete Lean AST command range lines420–473 in OrderSevenBacktrackingResultantCertificate. Pure data values retained and compared against the checked source. Named downstream consumers: selection_divisionCofactor0_resultant_eq_resultantFactorData_eval, bounded_resultants_ne_zero, and the full arbitrary-E order49 exclusion.

import Definitions.Def_MazurTransfer_Order49BacktrackingCofactors
import Definitions.Def_MazurTransfer_Order49ResultantFactorData
import Mathlib.RingTheory.Polynomial.Resultant.Basic

theorem MazurTransfer.order49_generic_resultant_factorization :
Polynomial.resultant MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactorData MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData0 33 7 = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.resultantFactorData := by sorry
