-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_full_fubini
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_full_fubini
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:55:32.760897+00:00
-- url     : https://prove2.me/theorems/4493a42d-d366-48a0-914f-579c2c2a52a3
-- title:
--   Apply Tonelli to the joint simplex region
-- statement:
--   Tonelli's theorem identifies the lower integral of the joint region's fiber volumes with the volume of the joint region. In each fiber, the cutoff on the coordinate sum is equivalent to the joint cutoff.

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_full_fubini (n : Nat) (T : Real) : (∫⁻ t : Real, MeasureTheory.volume {y : Fin n → Real | 0 ≤ t ∧ (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - t} ∂MeasureTheory.volume) = MeasureTheory.volume {z : Real × (Fin n → Real) | 0 ≤ z.1 ∧ (∀ i, 0 ≤ z.2 i) ∧ z.1 + (∑ i, z.2 i) < T} := by sorry
