-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_of_coordinate_isometry
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_volume_of_coordinate_isometry
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:33:56.519655+00:00
-- url     : https://prove2.me/theorems/a09aa44d-9263-453f-8347-bd71a70925ff
-- title:
--   Transfer simplex volume through coordinate splitting
-- statement:
--   For any linear isometry with the specified coordinate behavior, the two displayed regions have equal volume. The coordinate identities give equivalence of their defining inequalities after splitting the finite sum at the final coordinate. Then `LinearIsometryEquiv.measurePreserving` transfers volume. This handles `m = 0` and every real cutoff `T`.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators
open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.simplex_volume_of_coordinate_isometry (m : Nat) (T : Real)
    (e : ((Fin m → Real) × Real) ≃ₗᵢ[Real] (Fin (m + 1) → Real))
    (hfirst : ∀ p i, e p (Fin.castSucc i) = p.1 i)
    (hlast : ∀ p, e p (Fin.last m) = p.2) :
    MeasureTheory.volume {x : Fin (m + 1) → Real |
      (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} =
      MeasureTheory.volume {p : (Fin m → Real) × Real |
        (∀ i, 0 ≤ p.1 i) ∧ 0 ≤ p.2 ∧ (∑ i, p.1 i) + p.2 < T} := by sorry
