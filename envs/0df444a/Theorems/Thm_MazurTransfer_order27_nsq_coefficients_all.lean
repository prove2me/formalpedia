-- Prove2me | Theorems.Thm_MazurTransfer_order27_nsq_coefficients_all
-- name    : MazurTransfer.order27_nsq_coefficients_all
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T16:02:31.480305+00:00
-- url     : https://prove2.me/theorems/165e7e4c-a263-481d-b341-2fcf15a373c5
-- title:
--   Order-27 numerator-square coefficient formulas: all
-- statement:
--   For every rational parameter $f$ and every nonnegative coefficient index $n$, the displayed formulas give the exact coefficients of this group of fixed univariate polynomials. Each term contributes only at its specified index. These formulas cover the numerator, trisection, remainder and quotient families needed to check the final square-numerator identity. They impose no equation on $f$ or on a rational point.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Exact coefficient models of the original tlNSq_s3 quotient identity; original literal functions selected by Lean AST body ranges. Balanced coefficient matrices, all 26 evaluation bridges, and all 19 coefficient equalities checked with standard Lean axioms. Named downstream consumer: the unchanged complete order27_leaf_tlNSq_s3 statement.

import Definitions.Def_MazurTransfer_Order27NSqCoefficientData
open Polynomial MazurTransfer.Order27NSqPolynomial

theorem MazurTransfer.order27_nsq_coefficients_all :
∀ (f : ℚ) (n : ℕ),
((p_tlN0 f).coeff n = c_tlN0 f n) ∧
((p_tlN1 f).coeff n = c_tlN1 f n) ∧
((p_tlN2 f).coeff n = c_tlN2 f n) ∧
((p_tlN3 f).coeff n = c_tlN3 f n) ∧
((p_tlT0 f).coeff n = c_tlT0 f n) ∧
((p_tlT1 f).coeff n = c_tlT1 f n) ∧
((p_tlT2 f).coeff n = c_tlT2 f n) ∧
((p_tlT3 f).coeff n = c_tlT3 f n) ∧
((p_tlNSqP3c0 f).coeff n = c_tlNSqP3c0 f n) ∧
((p_tlNSqP3c1 f).coeff n = c_tlNSqP3c1 f n) ∧
((p_tlNSqP3c2 f).coeff n = c_tlNSqP3c2 f n) ∧
((p_tlNSqP3c3 f).coeff n = c_tlNSqP3c3 f n) ∧
((p_tlNSqP3c4 f).coeff n = c_tlNSqP3c4 f n) ∧
((p_tlNSqP3c5 f).coeff n = c_tlNSqP3c5 f n) ∧
((p_tlNSqP3c6 f).coeff n = c_tlNSqP3c6 f n) ∧
((p_tlNSqP3c7 f).coeff n = c_tlNSqP3c7 f n) ∧
((p_tlNSqP3c8 f).coeff n = c_tlNSqP3c8 f n) ∧
((p_tlNSqP3c9 f).coeff n = c_tlNSqP3c9 f n) ∧
((p_tlNSqP3c10 f).coeff n = c_tlNSqP3c10 f n) ∧
((p_tlNSqP3c11 f).coeff n = c_tlNSqP3c11 f n) ∧
((p_tlNSqQ3c0 f).coeff n = c_tlNSqQ3c0 f n) ∧
((p_tlNSqQ3c1 f).coeff n = c_tlNSqQ3c1 f n) ∧
((p_tlNSqQ3c2 f).coeff n = c_tlNSqQ3c2 f n) ∧
((p_tlNSqQ3c3 f).coeff n = c_tlNSqQ3c3 f n) ∧
((p_tlNSqQ3c4 f).coeff n = c_tlNSqQ3c4 f n) ∧
((p_tlNSqQ3c5 f).coeff n = c_tlNSqQ3c5 f n) := by sorry
