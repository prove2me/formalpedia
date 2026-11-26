-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_ucp_pathwise_subsequence_transfer
-- name    : Kyprianou.Ch04.ito43_ucp_pathwise_subsequence_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:55:04.156678+00:00
-- url     : https://prove2.me/theorems/f0053908-1983-5852-8ebb-c6656aeb8775
-- title:
--   UCP transfers through a measurable bounded pathwise subsequence limit
-- statement:
--   Extract an almost surely uniformly convergent further subsequence for the input. Apply the pathwise transfer and the supremum bound. Measurability of the output envelope is essential for the return to outer UCP.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_ucp_pathwise_subsequence_transfer {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (A B : ℕ → NNReal → Omega → ℝ) (T : NNReal)
    (hA : ∀ (e : ℝ), 0 < e →
      Tendsto (fun n => (P {w | ∃ t ≤ T, e ≤ |A n t w|}).toReal) atTop (nhds 0))
    (hMeas : ∀ n, AEStronglyMeasurable
      (fun w => sSup (Set.range (fun t : Set.Iic T => |B n t w|))) P)
    (hBdd : ∀ᵐ w ∂P, ∀ n, BddAbove (Set.range (fun t : Set.Iic T => |B n t w|)))
    (hTransfer : ∀ (N : ℕ → ℕ), Tendsto N atTop atTop →
      (∀ᵐ w ∂P, ∀ e : ℝ, 0 < e →
        ∀ᶠ n in atTop, ∀ t ≤ T, |A (N n) t w| < e) →
      ∀ᵐ w ∂P, ∀ e : ℝ, 0 < e →
        ∀ᶠ n in atTop, ∀ t ≤ T, |B (N n) t w| < e) :
    ∀ (e : ℝ), 0 < e →
      Tendsto (fun n => (P {w | ∃ t ≤ T, e ≤ |B n t w|}).toReal) atTop (nhds 0) := by sorry
