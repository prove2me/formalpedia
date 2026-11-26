-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_ucp_extract_ae_subsequence
-- name    : Kyprianou.Ch04.ito43_ucp_extract_ae_subsequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:55:07.935987+00:00
-- url     : https://prove2.me/theorems/ae24b26b-1503-4929-a6b8-748e8fd3cfec
-- title:
--   Outer UCP convergence admits an almost sure uniform further subsequence
-- statement:
--   Choose a further subsequence of any divergent sequence of indices with summable outer error-event probabilities at geometric tolerances. Apply Borel Cantelli without assuming the error events measurable.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_ucp_extract_ae_subsequence {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (A : ℕ → NNReal → Omega → ℝ) (T : NNReal)
    (hA : ∀ (e : ℝ), 0 < e →
      Tendsto (fun n => (P {w | ∃ t ≤ T, e ≤ |A n t w|}).toReal) atTop (nhds 0))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    ∃ M : ℕ → ℕ, Tendsto M atTop atTop ∧
      ∀ᵐ w ∂P, ∀ e : ℝ, 0 < e →
        ∀ᶠ n in atTop, ∀ t ≤ T, |A (N (M n)) t w| < e := by sorry
