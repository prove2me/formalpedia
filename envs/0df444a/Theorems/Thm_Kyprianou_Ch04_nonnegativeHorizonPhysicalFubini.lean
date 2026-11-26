-- Prove2me | Theorems.Thm_Kyprianou_Ch04_nonnegativeHorizonPhysicalFubini
-- name    : Kyprianou.Ch04.nonnegativeHorizonPhysicalFubini
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:44:14.0403+00:00
-- url     : https://prove2.me/theorems/9d51f8e1-b337-562a-9f98-d394d470ec2b
-- title:
--   nonnegativeHorizonPhysicalFubini
-- statement:
--   The physical reference-intensity integral on a finite horizon equals the nested time-mark integral for nonnegative jointly measurable kernels with finite expected integral.
-- source:
--   Kyprianou (2006), Exercise 4.4

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Identify the physical intensity integral with the nested time-mark integral. -/
theorem Kyprianou.Ch04.nonnegativeHorizonPhysicalFubini
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    (nu : Measure ℝ) [SigmaFinite nu] (t : NNReal)
    (f : Omega → ℝ × ℝ → ℝ)
    (hf : Measurable (fun z : Omega × (ℝ × ℝ) => f z.1 z.2))
    (hn : ∀ w z, 0 ≤ f w z)
    (hFin : (∫⁻ w, ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
      ∫⁻ x, ENNReal.ofReal (f w (s,x)) ∂nu ∂volume ∂P) < ⊤) :
    (∀ w, (∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
      ENNReal.ofReal (f w z) ∂referenceIntensity nu) =
      ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ), ∫⁻ x,
        ENNReal.ofReal (f w (s,x)) ∂nu ∂volume) ∧
    (∀ᵐ w ∂P, (∫ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
      f w z ∂referenceIntensity nu) =
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ), ∫ x, f w (s,x) ∂nu ∂volume) := by
  sorry
