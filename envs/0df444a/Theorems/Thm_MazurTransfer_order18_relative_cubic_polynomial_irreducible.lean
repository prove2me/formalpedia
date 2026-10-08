-- Prove2me | Theorems.Thm_MazurTransfer_order18_relative_cubic_polynomial_irreducible
-- name    : MazurTransfer.order18_relative_cubic_polynomial_irreducible
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T14:46:06.67041+00:00
-- url     : https://prove2.me/theorems/7e3f0648-1e9a-48cb-b938-4db2b3236d2c
-- title:
--   Order18: the relative two-division cubic remains irreducible over the real coefficient field
-- statement:
--   The polynomial \(S^3-3S-10\) is irreducible over \(K=\mathbb{Q}[T]/(T^3-3T-1)\).
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c. The exact original supporting theorem is selected by its typed kernel closure and complete original parsed source declarations. Original Apache-2.0 headers and attribution retained. Named downstream consumers: both genuine halves of the full order18 arithmetic proof. No resource-strengthening options, custom axioms or modified hypotheses.

import Mathlib
import Definitions.Def_MazurTransfer_Order18RelativeCubicPolynomialData

theorem MazurTransfer.order18_relative_cubic_polynomial_irreducible : Irreducible MazurTorsion.XOneEighteenTwoDivisionArithmetic.relativePolynomial := by sorry
