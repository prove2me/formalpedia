-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_grid_energy_markov_bound
-- name    : Kyprianou.Ch04.ito43_grid_energy_markov_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:04:28.891239+00:00
-- url     : https://prove2.me/theorems/1fe1501c-143b-43c6-82e8-b08a7e339c89
-- title:
--   Markov tail for nonnegative variables with bounded mean
-- statement:
--   Markov tail for nonnegative variables with bounded mean.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal
set_option autoImplicit false
/-- A nonnegative integrable variable with bounded mean has a uniform Markov tail. -/

theorem Kyprianou.Ch04.ito43_grid_energy_markov_bound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Ω → ℝ) (hFi : Integrable F P) (hF0 : ∀ w, 0 ≤ F w)
    (K η : ℝ) (hK : 0 ≤ K) (hη : 0 < η)
    (hmean : (∫ w, F w ∂P) ≤ K) :
    (P {w | 2*K/η+1 ≤ F w}).toReal ≤ η/2 := by sorry
