-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_arctangent_fdd_limit_is_interior_on_compact_rational_times
-- name    : ManyServerQED.Scheduling.arctangent_fdd_limit_is_interior_on_compact_rational_times
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T03:34:04.918515+00:00
-- url     : https://prove2.me/theorems/261a8af0-3e51-58cb-84ba-614d3870ee8c
-- title:
--   Interior margins in limits of arctangent observations
-- statement:
--   If path sup norms are bounded in probability on each compact time interval and the finite-dimensional laws of the coordinatewise arctangents converge, then the limit arctangents stay a positive distance from both endpoint values on the rational times of each compact interval, almost surely.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
open Filter Topology Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem ManyServerQED.Scheduling.arctangent_fdd_limit_is_interior_on_compact_rational_times {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {k : ℕ} (X : ℕ → Ω → ℝ → Fin k → ℝ) (y : Ω' → ℝ → Fin k → ℝ)
    (hF : ∀ (m : ℕ) (τ : Fin m → ℝ), (∀ j, 0 ≤ τ j) →
      TendstoInDistribution (fun n ω j i => Real.arctan (X n ω (τ j) i)) atTop
        (fun ω j => y ω (τ j)) (fun _ => P) P')
    (hB : ∀ (T : ℕ) (η : ℝ), 0 < η → ∃ A ≥ (0:ℝ), ∀ᶠ n in atTop,
      P {ω | ∃ t ∈ Icc (0:ℝ) (T:ℝ), A < ‖X n ω t‖} ≤ ENNReal.ofReal η) :
    ∀ᵐ ω ∂P', ∀ (T : ℕ) (i : Fin k), ∃ b : ℕ, ∀ q : ℚ,
      (q:ℝ) ∈ Icc (0:ℝ) (T:ℝ) → |y ω (q:ℝ) i| ≤ Real.pi/2-1/((b:ℝ)+1) := by sorry
