-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_region_interval_support_fiber_eq_inside
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_region_interval_support.fiber_eq_inside
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:35:29.164141+00:00
-- url     : https://prove2.me/theorems/272db393-7fa5-48f5-afa0-6a3deac58522
-- title:
--   The constrained and unconstrained fibers agree in the open interval
-- statement:
--   For an interior parameter, the constraint `0 ≤ t` is automatic, so the constrained and unconstrained fiber sets, and hence their volumes, agree.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_region_interval_support.fiber_eq_inside (m : Nat) (H t : Real) (ht0 : 0 < t) (htH : t < H) :
    (MeasureTheory.volume {x : Fin m → Real | 0 ≤ t ∧ (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H - t}).toReal =
      (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H - t}).toReal := by sorry
