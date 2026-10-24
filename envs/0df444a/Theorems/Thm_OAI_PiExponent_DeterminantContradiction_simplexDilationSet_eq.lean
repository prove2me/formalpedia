-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexDilationSet_eq
-- name    : OAI.PiExponent.DeterminantContradiction.simplexDilationSet_eq
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:10:31.559273+00:00
-- url     : https://prove2.me/theorems/d098678a-3b78-49c1-a08b-51792d45fbf3
-- title:
--   Coordinate simplex as a scalar image
-- statement:
--   The coordinate simplex with nonnegative bound `c` is the image of the unit coordinate simplex under scalar multiplication by `c`, including zero bound and dimension zero.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexDilationSet_eq (n : Nat) (c : Real) (hc : 0 ≤ c) :
    {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i : Fin n, x i) ≤ c} =
      (fun x : Fin n → Real => c • x) ''
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i : Fin n, x i) ≤ 1} := by sorry
