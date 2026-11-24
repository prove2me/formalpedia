-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stableGridUnboundedFromLaplaceV1
-- name    : Kyprianou.Ch03.stableGridUnboundedFromLaplaceV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T18:19:12.937061+00:00
-- url     : https://prove2.me/theorems/27a16c6d-6896-4cd8-b7ea-b029c49ecf47
-- title:
--   Vanishing grid Laplace expectations imply almost sure unboundedness
-- statement:
--   If nonnegative grid sums have Laplace expectations tending to zero, their supremum is almost surely infinite. Apply a probability bound to each countable integer threshold.
-- source:
--   Auxiliary probability lemma for Kyprianou (2006), Exercise 3.7.

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

theorem Kyprianou.Ch03.stableGridUnboundedFromLaplaceV1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, AEMeasurable (Y n) P) (hnon : ∀ n, 0 ≤ᵐ[P] Y n)
    (hlim : Tendsto (fun n => ∫ w, Real.exp (-Y n w) ∂P) atTop (𝓝 0)) :
    ∀ᵐ w ∂P, ∀ M : ℝ, ∃ n : ℕ, M < Y n w := by sorry
