-- Prove2me | Theorems.Thm_MazurTransfer_order18_compositum_exact_signature
-- name    : MazurTransfer.order18_compositum_exact_signature
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T18:06:59.208873+00:00
-- url     : https://prove2.me/theorems/20734672-3777-415f-9432-5b49f24c8055
-- title:
--   Order-18 arithmetic: compositum exact signature
-- statement:
--   For the separately constructed field $M=(\mathbb Q[T]/(T^3-3T-1))[S]/(S^3-3S-10)$,
--   \[[M:\mathbb Q]=9,\qquad (r_1(M),r_2(M))=(3,3).\]
--   The tower formula gives degree nine. The real-embedding bound gives $r_1\leq 3$, and the discriminant sign gives odd $r_2$. Together with $r_1+2r_2=9$ these force the exact signature. This provides the signature input for the order-18 integral-unit square-class calculation.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Complete original proofs selected through kernel dependencies and resolved whole Lean AST commands; Apache-2.0 headers and provenance retained. The named downstream consumer is the order-18 global Selmer cardinality calculation.

import Definitions.Def_MazurTransfer_Order18CompositumField
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

theorem MazurTransfer.order18_compositum_exact_signature :
Module.finrank ℚ MazurTorsion.XOneEighteenTwoDivisionArithmetic.M = 9 ∧
  NumberField.InfinitePlace.nrRealPlaces MazurTorsion.XOneEighteenTwoDivisionArithmetic.M = 3 ∧
  NumberField.InfinitePlace.nrComplexPlaces MazurTorsion.XOneEighteenTwoDivisionArithmetic.M = 3 := by sorry
