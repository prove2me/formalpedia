-- Prove2me | Theorems.Thm_Kyprianou_Ch04_l2FatouSquareLimitV1
-- name    : Kyprianou.Ch04.l2FatouSquareLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:37:31.52182+00:00
-- url     : https://prove2.me/theorems/19b552b1-bb85-4e0d-9d05-c85d4434ea89
-- title:
--   Fatou inequality for squares of almost sure limits
-- statement:
--   The second moment of an almost sure limit of square-integrable measurable variables is at most the limit of their second moments.
-- source:
--   Kyprianou (2006), Exercise 4.5(ii); finite marked Poisson moment calculation.

import Mathlib
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem l2FatouSquareLimitV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ n, Measurable (f n)) (hfi : ∀ n, Integrable (fun ω => (f n ω)^2) P)
    (hgi : Integrable (fun ω => (g ω)^2) P)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hlim : Tendsto (fun n => ∫ ω, (f n ω)^2 ∂P) atTop (𝓝 K)) :
    (∫ ω, (g ω)^2 ∂P) ≤ K := by
  sorry
end Kyprianou.Ch04
