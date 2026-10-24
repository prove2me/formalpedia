-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_coordinate_reindex_isometry
-- name    : OAI.PiExponent.DeterminantContradiction.coordinate_reindex_isometry
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:33:45.648993+00:00
-- url     : https://prove2.me/theorems/648b9243-b0fa-4331-b4a4-7c5620174592
-- title:
--   Construct the coordinate-splitting linear isometry
-- statement:
--   Construct a linear isometry from the product of the first `m` real coordinates and one final real coordinate to `Fin (m+1) → Real`, with the stated coordinate behavior. The assertion also covers `m = 0`. A proof can compose the standard finite-coordinate splitting equivalence with the corresponding coordinate permutation; both preserve the sum-of-squares norm.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators
open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.coordinate_reindex_isometry (m : Nat) :
    ∃ e : ((Fin m → Real) × Real) ≃ₗᵢ[Real] (Fin (m + 1) → Real),
      (∀ p i, e p (Fin.castSucc i) = p.1 i) ∧
      (∀ p, e p (Fin.last m) = p.2) := by sorry
