-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_succ_product_reindex
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_volume_succ_product_reindex
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:27:59.971079+00:00
-- url     : https://prove2.me/theorems/eabaafce-d268-426d-9d49-d14baf19c4f3
-- title:
--   Reindex the simplex as a product region
-- statement:
--   Reindex the m+1 coordinates as the first m coordinates together with one real coordinate, and show that this coordinate permutation preserves Lebesgue volume. The finite-coordinate measurable equivalence provides a direct proof route, including when m = 0. This removes the coordinate-space identification from the parent.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators
open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.simplex_volume_succ_product_reindex (m : Nat) (T : Real) :
    MeasureTheory.volume {x : Fin (m + 1) → Real |
      (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} =
      MeasureTheory.volume {p : (Fin m → Real) × Real |
        (∀ i, 0 ≤ p.1 i) ∧ 0 ≤ p.2 ∧ (∑ i, p.1 i) + p.2 < T} := by sorry
