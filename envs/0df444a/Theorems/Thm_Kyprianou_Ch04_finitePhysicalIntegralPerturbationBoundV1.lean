-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finitePhysicalIntegralPerturbationBoundV1
-- name    : Kyprianou.Ch04.finitePhysicalIntegralPerturbationBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:06:50.617167+00:00
-- url     : https://prove2.me/theorems/9e8d7cfa-3704-4d22-9d28-9bfcf4467006
-- title:
--   finitePhysicalIntegralPerturbationBoundV1
-- statement:
--   finitePhysicalIntegralPerturbationBoundV1
-- source:
--   Kyprianou (2006), Exercise 4.5(iii), uniform finite variation error

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finitePhysicalAtomsSubwindowIntegralV1
open MeasureTheory Set
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- The large-jump integral perturbation is bounded by the finite absolute mark ledger. -/

theorem Kyprianou.Ch04.finitePhysicalIntegralPerturbationBoundV1 (R : Measure (ℝ × ℝ)) (T : NNReal)
    (S : Finset NNReal) (j H L : NNReal → ℝ)
    (hS : ∀ r ∈ S, 0 < r ∧ r ≤ T)
    (hR : R.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1/2 < |x|}) =
      ∑ r ∈ S, Measure.dirac ((r : ℝ),j r))
    (d : ℝ) (hd : 0 ≤ d)
    (h : ∀ r ≤ T, 0 < r → |H r - L r| ≤ d) :
    ∀ t ≤ T, |(∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
        z.2 * H z.1.toNNReal ∂ R) -
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
        z.2 * L z.1.toNNReal ∂ R)| ≤ (∑ r ∈ S, |j r|)*d := by
  sorry
