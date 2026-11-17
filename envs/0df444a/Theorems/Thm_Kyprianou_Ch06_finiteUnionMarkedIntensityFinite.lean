-- Prove2me | Theorems.Thm_Kyprianou_Ch06_finiteUnionMarkedIntensityFinite
-- name    : Kyprianou.Ch06.finiteUnionMarkedIntensityFinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T11:48:08.663199+00:00
-- url     : https://prove2.me/theorems/ccd13f0b-c245-4e3f-9ad5-c0e8c219cd1f
-- title:
--   Finite union of measurable finite-intensity mark sets has finite marked-Poisson intensity
-- statement:
--   For any measure n on the original mark space and any finite family of measurable sets B_i each having finite n-intensity, their union is measurable and has finite n-intensity. This follows from the finite-subadditivity upper bound by the finite sum of n(B_i). The lemma preserves the original per-coordinate assumptions and is used to reduce arbitrary finite simultaneous outside mark zero-count cylinders to a single measurable finite-intensity union.

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.finiteUnionMarkedIntensityFinite
    {E : Type} [MeasurableSpace E]
    (n : Measure E) (m : Nat) (B : Fin m → Set E)
    (hB : ∀ i, MeasurableSet (B i) ∧ n (B i) < ⊤) :
    MeasurableSet (⋃ i, B i) ∧ n (⋃ i, B i) < ⊤ := by sorry
