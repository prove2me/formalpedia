-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_product_lintegral
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_product_lintegral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:28:12.781333+00:00
-- url     : https://prove2.me/theorems/f17f9592-e81d-4f0d-9106-9bf0884b8824
-- title:
--   Integrate the product-coordinate simplex sections
-- statement:
--   Apply Tonelli to the indicator of the measurable simplex region in product coordinates. For each t, the first-coordinate section is empty outside 0 ≤ t < T; inside that range, splitting the sum yields the m-dimensional simplex with threshold T − t. This supplies the product-measure integration step needed by the parent.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators
open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.simplex_product_lintegral (m : Nat) (T : Real) :
    MeasureTheory.volume {p : (Fin m → Real) × Real |
      (∀ i, 0 ≤ p.1 i) ∧ 0 ≤ p.2 ∧ (∑ i, p.1 i) + p.2 < T} =
      MeasureTheory.lintegral MeasureTheory.volume (fun t : Real =>
        if 0 ≤ t ∧ t < T then
          MeasureTheory.volume {x : Fin m → Real |
            (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T - t}
        else 0) := by sorry
