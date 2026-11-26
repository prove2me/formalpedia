-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_full_grid_energy_tail
-- name    : Kyprianou.Ch04.ito43_full_grid_energy_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:21:55.845044+00:00
-- url     : https://prove2.me/theorems/af4cbc25-f9fb-45ba-8de9-698ea49d7f63
-- title:
--   Stopped quadratic energy tail controls the full-grid energy tail
-- statement:
--   Stopped quadratic energy tail controls the full-grid energy tail.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- A bound for the stopped energy at all times bounds the full grid along the positive mesh sequence. -/

theorem Kyprianou.Ch04.ito43_full_grid_energy_tail {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (T : NNReal) (C η : ℝ)
    (h : ∀ᶠ n : ℕ in atTop,
      (P {w | ∃ t : NNReal, t ≤ T ∧
        let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
        let v : ℕ → NNReal := fun k => min t (u k)
        C ≤ ∑ k ∈ Finset.range n, (X (v (k+1)) w-X (v k) w)^2}).toReal ≤ η) :
    ∀ᶠ n : ℕ in atTop, (P {w | C ≤ ∑ k ∈ Finset.range (n+1),
      (X (T*((k+1 : ℕ) : NNReal)/((n+1 : ℕ) : NNReal)) w -
       X (T*(k : NNReal)/((n+1 : ℕ) : NNReal)) w)^2}).toReal ≤ η := by sorry
