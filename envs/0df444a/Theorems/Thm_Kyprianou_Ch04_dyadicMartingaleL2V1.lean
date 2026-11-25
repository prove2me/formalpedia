-- Prove2me | Theorems.Thm_Kyprianou_Ch04_dyadicMartingaleL2V1
-- name    : Kyprianou.Ch04.dyadicMartingaleL2V1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:25:01.194074+00:00
-- url     : https://prove2.me/theorems/c141d2d7-83a4-58cb-863e-8edb26f36490
-- title:
--   Dyadic L2 maximal estimate without path continuity
-- statement:
--   For any real martingale on nonnegative real time with square-integrable terminal value, each finite dyadic maximum of the squared process is integrable and its expectation is at most four times the terminal second moment. No continuity assumption is needed.
-- source:
--   Kyprianou (2006), Exercise 4.5(ii); discrete Doob inequality.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem dyadicMartingaleL2V1
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M : ℝ≥0 → Ω → ℝ)
    (hMart : Martingale M 𝓕 P)
    (T : ℝ≥0)
    (hL2 : Integrable (fun ω => (M T ω)^2) P) :
    ∀ k : ℕ,
      Integrable (fun ω =>
        (Finset.range (2^k + 1)).sup'
          (by simp) (fun i =>
            (M ((i : ℝ≥0) * T / (2^k : ℝ≥0)) ω)^2)) P ∧
      (∫ ω,
        (Finset.range (2^k + 1)).sup'
          (by simp) (fun i =>
            (M ((i : ℝ≥0) * T / (2^k : ℝ≥0)) ω)^2) ∂P) ≤
        4 * (∫ ω, (M T ω)^2 ∂P) := by
  sorry
end Kyprianou.Ch04
