-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_real_step_partition
-- name    : Kyprianou.Ch04.ito43_real_step_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:17:28.2154+00:00
-- url     : https://prove2.me/theorems/21e1b390-7d1b-5ba8-a67d-ae4e0a54b12f
-- title:
--   Càdlàg real path admits finite threshold approximation
-- statement:
--   Use Billingsley’s finite small-oscillation partition; choose coefficients as differences of consecutive sampled values.
-- source:
--   Kyprianou (2006), Theorem 4.3 proof auxiliary

import Mathlib
import Definitions.Def_WhittFLT_Composition_SkorohodD
open Set Filter
open scoped Topology ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_real_step_partition
    (Y : ℝ → ℝ) (U : ℝ) (hU : 0 < U)
    (hY : WhittFLT.Composition.IsCadlagOn (Icc 0 U) Y)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (m : ℕ) (b c : ℕ → ℝ), (∀ i, 0 ≤ b i) ∧
      ∀ s, 0 ≤ s → s < U →
        |Y s - ∑ i ∈ Finset.range m, c i * (if b i ≤ s then (1:ℝ) else 0)| ≤ δ := by sorry
