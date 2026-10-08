-- Prove2me | Theorems.Thm_MazurTransfer_order18_rational_cubics_irreducible
-- name    : MazurTransfer.order18_rational_cubics_irreducible
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T17:42:16.313008+00:00
-- url     : https://prove2.me/theorems/f5236fd1-ca34-409a-83e4-19f9dca159b6
-- title:
--   Order-18 field validity: rational irreducibility
-- statement:
--   The two fixed rational cubics are irreducible:
--   \[p(T)=T^3-3T-1,\qquad q(S)=S^3-3S-10\quad\text{are irreducible over }\mathbb Q.\]
--   The first cubic is certified by reduction modulo two and the second by reduction modulo eleven. These are the constructor-validity inputs for the exact coefficient and two-division fields of the order-18 descent.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Complete original algebraic-number-field validity proofs selected by kernel dependencies and resolved whole Lean AST commands. Original Apache-2.0 headers retained; no numerical oracle or class-number assertion is assumed.

import Definitions.Def_MazurTransfer_Order18RationalCubics

theorem MazurTransfer.order18_rational_cubics_irreducible :
Irreducible MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial ∧
  Irreducible MazurTorsion.XOneEighteenTwoDivisionArithmetic.twoDivisionPolynomial := by sorry
