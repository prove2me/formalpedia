-- Prove2me | Theorems.Thm_MazurTransfer_order18_relative_two_division_irreducible
-- name    : MazurTransfer.order18_relative_two_division_irreducible
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T17:47:57.333006+00:00
-- url     : https://prove2.me/theorems/8ba744dd-8ab9-4dcc-92ad-8c6ea8c4dbc6
-- title:
--   Order-18 field validity: relative irreducibility
-- statement:
--   Let $K=\mathbb Q[T]/(T^3-3T-1)$ with its separately checked field structure. Then
--   \[S^3-3S-10\quad\text{is irreducible over }K.\]
--   The proof compares the exact power-basis discriminants $81$ and $-2592$, which exclude an embedding of the two rational cubic fields into one another. This supplies the field-validity witness for the degree-nine two-division compositum. It assumes no class-number or Selmer conclusion.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Complete original algebraic-number-field validity proofs selected by kernel dependencies and resolved whole Lean AST commands. Original Apache-2.0 headers retained; no numerical oracle or class-number assertion is assumed.

import Definitions.Def_MazurTransfer_Order18RelativeAlgebra

theorem MazurTransfer.order18_relative_two_division_irreducible :
Irreducible MazurTorsion.XOneEighteenTwoDivisionArithmetic.relativePolynomial := by sorry
