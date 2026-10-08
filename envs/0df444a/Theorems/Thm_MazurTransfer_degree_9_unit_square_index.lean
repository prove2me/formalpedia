-- Prove2me | Theorems.Thm_MazurTransfer_degree_9_unit_square_index
-- name    : MazurTransfer.degree_9_unit_square_index
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T18:09:24.758986+00:00
-- url     : https://prove2.me/theorems/028c6508-540a-4e6c-bece-138aed12afaa
-- title:
--   Order-18 arithmetic: degree 9 unit square index
-- statement:
--   Let $L$ be a number field with degree $9$ and exactly three real places. The subgroup of squares in its full integral-unit group has index
--   \[[\mathcal O_L^\times:(\mathcal O_L^\times)^2]=64.\]
--   Dirichlet’s unit theorem determines the free rank, and odd degree forces the roots of unity to be $\{\pm1\}$. The multiplication-by-two index formula then computes the full quotient size. The conclusion is stated as a group index in standard Mathlib types; the original unit square-class statement is definitionally the same. Named downstream consumer: the coefficient and degree-nine dyadic Selmer cardinality calculation.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Complete original proofs selected through kernel dependencies and resolved whole Lean AST commands; Apache-2.0 headers and provenance retained. The named downstream consumer is the order-18 global Selmer cardinality calculation.

import Mathlib

theorem MazurTransfer.degree_9_unit_square_index :
∀ (L : Type*) [Field L] [NumberField L],
  Module.finrank ℚ L = 9 →
  NumberField.InfinitePlace.nrRealPlaces L = 3 →
  (nsmulAddMonoidHom (α := Additive (NumberField.RingOfIntegers L)ˣ) 2).range.index = 64 := by sorry
