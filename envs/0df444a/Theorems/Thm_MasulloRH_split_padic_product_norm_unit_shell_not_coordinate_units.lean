-- Prove2me | Theorems.Thm_MasulloRH_split_padic_product_norm_unit_shell_not_coordinate_units
-- name    : MasulloRH.split_padic_product_norm_unit_shell_not_coordinate_units
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T10:19:37.248849+00:00
-- url     : https://prove2.me/theorems/bba82b16-4ccc-4855-bb25-aa2adb5fe437
-- title:
--   A positive-measure split p-adic shell has unit product norm and neither coordinate is an integral unit
-- statement:
--   For every prime p the open shell in Q_p × Q_p with local absolute values 1/p and p contains (p,1/p). Every measure positive on open sets gives it positive mass. Its multiplicative norm xy is a p-adic integral unit, although neither coordinate is an integral unit.
-- source:
--   Comparison of the norm pullback with the placewise-unit stratum in Masullo section 11.3.1 over a split prime of a quadratic field. The field norm on the split local algebra is multiplication.

import Mathlib
open MeasureTheory

theorem MasulloRH.split_padic_product_norm_unit_shell_not_coordinate_units (p : ℕ) [hp : Fact p.Prime]
    [MeasurableSpace (ℚ_[p] × ℚ_[p])]
    (μ : Measure (ℚ_[p] × ℚ_[p])) [μ.IsOpenPosMeasure] :
    let S : Set (ℚ_[p] × ℚ_[p]) :=
      {z | ‖z.1‖ = (p : ℝ)⁻¹ ∧ ‖z.2‖ = (p : ℝ)}
    IsOpen S ∧ ((p : ℚ_[p]),(p : ℚ_[p])⁻¹) ∈ S ∧ 0 < μ S ∧
      ∀ z ∈ S, ‖z.1 * z.2‖ = 1 ∧
        (∃ v : ℤ_[p]ˣ, ((v : ℤ_[p]) : ℚ_[p]) = z.1 * z.2) ∧
        ∀ u : ℤ_[p]ˣ, ((u : ℤ_[p]) : ℚ_[p]) ≠ z.1 ∧
          ((u : ℤ_[p]) : ℚ_[p]) ≠ z.2 := by sorry
