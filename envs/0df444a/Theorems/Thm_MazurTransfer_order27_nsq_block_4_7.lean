-- Prove2me | Theorems.Thm_MazurTransfer_order27_nsq_block_4_7
-- name    : MazurTransfer.order27_nsq_block_4_7
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T16:18:37.402671+00:00
-- url     : https://prove2.me/theorems/233f8b24-acb6-4895-b7ee-fcb2fbad81c5
-- title:
--   Order-27 final square-numerator identity: coefficients 4–7
-- statement:
--   For every rational parameter $f$, the coefficients numbered 4 through 7 of the two fixed univariate polynomials agree. The left polynomial is $N_3\sum_i N_i$; the right is the remainder sum plus the quotient sum times $\sum_iT_i$. This is a universal polynomial identity in the parameter, not a check at finitely many parameter values. Together, the coefficient blocks and degree bounds give the complete polynomial equality.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Exact coefficient models of the original tlNSq_s3 quotient identity; original literal functions selected by Lean AST body ranges. Balanced coefficient matrices, all 26 evaluation bridges, and all 19 coefficient equalities checked with standard Lean axioms. Named downstream consumer: the unchanged complete order27_leaf_tlNSq_s3 statement.

import Definitions.Def_MazurTransfer_Order27NSqCoefficientData
open Polynomial MazurTransfer.Order27NSqPolynomial

theorem MazurTransfer.order27_nsq_block_4_7 :
∀ (f : ℚ),
((leftSide f).coeff 4 = (rightSide f).coeff 4) ∧
((leftSide f).coeff 5 = (rightSide f).coeff 5) ∧
((leftSide f).coeff 6 = (rightSide f).coeff 6) ∧
((leftSide f).coeff 7 = (rightSide f).coeff 7) := by sorry
