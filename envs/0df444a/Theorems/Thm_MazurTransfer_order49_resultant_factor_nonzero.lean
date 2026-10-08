-- Prove2me | Theorems.Thm_MazurTransfer_order49_resultant_factor_nonzero
-- name    : MazurTransfer.order49_resultant_factor_nonzero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T21:56:11.392968+00:00
-- url     : https://prove2.me/theorems/ba94f10d-b3ab-4dfe-b25f-84548f271a2b
-- title:
--   Order-49 factored resultant is nonzero at every nonsingular parameter
-- statement:
--   Let $f_6,f_{12}\in\mathbb Z[T]$ and $F(T)=T^{63}(T-1)^{51}(T^3-8T^2+5T+1)^{260}f_6(T)^2f_{12}(T)$ be the fixed resultant-factor data. For every $d\in\mathbb Q$ with $d\ne0$, $d\ne1$ and $d^3-8d^2+5d+1\ne0$, $$F(d)\ne0.$$ This isolates the rational nonvanishing needed to specialize the generic resultant certificate.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0 original headers retained. Exact original MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.resultantFactorData_eval_ne_zero statement and checked original helper proofs retained at complete original Lean AST command boundaries. No assumptions or coefficient data altered. Named downstream consumers: bounded_resultants_ne_zero and the full arbitrary-E order49 exclusion.

import Definitions.Def_MazurTransfer_Order49BacktrackingCofactors
import Definitions.Def_MazurTransfer_Order49ResultantFactorData
import Mathlib.RingTheory.Polynomial.Resultant.Basic

theorem MazurTransfer.order49_resultant_factor_nonzero
    (d : ℚ) (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hcubic : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0) :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.resultantFactorData.eval d ≠ 0 := by sorry
