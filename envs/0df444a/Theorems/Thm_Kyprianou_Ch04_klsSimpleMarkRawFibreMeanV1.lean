-- Prove2me | Theorems.Thm_Kyprianou_Ch04_klsSimpleMarkRawFibreMeanV1
-- name    : Kyprianou.Ch04.klsSimpleMarkRawFibreMeanV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:37:35.940645+00:00
-- url     : https://prove2.me/theorems/e130841e-f8b4-4ce4-8862-e958da5524ea
-- title:
--   KLS simple mark raw expectation as fibre sum
-- statement:
--   The expected raw simple-mark integral equals the sum of expected time-mark fibre counts multiplied by each mark value.
-- source:
--   Kyprianou (2006), Exercise 4.5(ii); finite marked Poisson moment calculation.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem klsSimpleMarkRawFibreMeanV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν) (B : Set ℝ)
    (hB : MeasurableSet B) (hfinite : ν B < ⊤) (g : SimpleFunc ℝ ℝ) (t : ℝ≥0) :
    (∫ ω, (∫ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ B, g z.2 ∂(N.N ω)) ∂P) =
      ∑ r ∈ g.range, ((t : ℝ) * (ν (B ∩ g ⁻¹' {r})).toReal) * r := by
  sorry
end Kyprianou.Ch04
