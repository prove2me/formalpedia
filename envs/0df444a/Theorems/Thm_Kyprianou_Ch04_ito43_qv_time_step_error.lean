-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_qv_time_step_error
-- name    : Kyprianou.Ch04.ito43_qv_time_step_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:29:03.861881+00:00
-- url     : https://prove2.me/theorems/a46b1746-bc05-5521-9cf6-5ed75b7d11a3
-- title:
--   Time step approximation error is bounded by interval mass
-- statement:
--   Use finite-step integral linearity and threshold interval masses; integrate the uniform error against the finite interval volume.
-- source:
--   Kyprianou (2006), Theorem 4.3 proof auxiliary

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_qv_time_step_error
    (Y : ℝ → ℝ) (t : NNReal) (hY : IntegrableOn Y (Icc (0:ℝ) (t:ℝ)) volume)
    (δ : ℝ) (m : ℕ) (b : ℕ → NNReal) (c : ℕ → ℝ)
    (hW : ∀ s ∈ Icc (0:ℝ) (t:ℝ),
      |Y s - ∑ i ∈ Finset.range m, c i * (if (b i:ℝ) ≤ s then (1:ℝ) else 0)| ≤ δ) :
    |(∫ s in Icc (0:ℝ) (t:ℝ), Y s ∂volume) -
      ∑ i ∈ Finset.range m, c i *
        ((∫ s in Icc (0:ℝ) (t:ℝ), (1:ℝ) ∂volume) -
          ∫ s in Icc (0:ℝ) ((min t (b i):NNReal):ℝ), (1:ℝ) ∂volume)| ≤
      δ * (t:ℝ) := by sorry
