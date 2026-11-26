-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_ucp_approximation
-- name    : Kyprianou.Ch04.ito43_ucp_approximation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:55:28.44739+00:00
-- url     : https://prove2.me/theorems/eb77a758-6243-503a-8763-055de299e831
-- title:
--   Uniform-in-probability convergence from convergent truncations and vanishing tails
-- statement:
--   Uniform-in-probability convergence from convergent truncations and vanishing tails.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Uniform-in-probability convergence follows from convergent truncations and vanishing tails. -/

theorem Kyprianou.Ch04.ito43_ucp_approximation {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ℕ → NNReal → Ω → ℝ) (A B : ℕ → ℕ → NNReal → Ω → ℝ) (T : NNReal)
    (hE : ∀ m n t w, E n t w = A m n t w + B m n t w)
    (hAl : ∀ (m : ℕ) (e : ℝ), 0 < e → Tendsto
      (fun n => (P {w | ∃ t ≤ T, e ≤ |A m n t w|}).toReal) atTop (nhds 0))
    (hB : ∀ e : ℝ, 0 < e → ∀ η : ℝ, 0 < η → ∃ m : ℕ,
      ∀ᶠ n in atTop, (P {w | ∃ t ≤ T, e ≤ |B m n t w|}).toReal ≤ η)
    (e : ℝ) (he : 0 < e) :
    Tendsto (fun n => (P {w | ∃ t ≤ T, e ≤ |E n t w|}).toReal) atTop (nhds 0) := by sorry
