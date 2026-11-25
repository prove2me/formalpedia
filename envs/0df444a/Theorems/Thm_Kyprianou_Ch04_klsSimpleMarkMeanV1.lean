-- Prove2me | Theorems.Thm_Kyprianou_Ch04_klsSimpleMarkMeanV1
-- name    : Kyprianou.Ch04.klsSimpleMarkMeanV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:35:43.14595+00:00
-- url     : https://prove2.me/theorems/e9dd2d63-0fdf-4bb6-b398-dbb1792e369e
-- title:
--   KLS signed simple marked integral exact Campbell first moment
-- statement:
--   For the modular KLS Poisson family, the expected raw signed simple-mark integral over a finite-intensity time-mark window is its time length times the intensity integral of the mark.
-- source:
--   Kyprianou (2006), Exercise 4.5(ii); finite-region Campbell identity.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedIsometry
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem klsSimpleMarkMeanV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν) (B : Set ℝ)
    (hB : MeasurableSet B) (hfinite : ν B < ⊤) (g : SimpleFunc ℝ ℝ) (t : ℝ≥0) :
    (∫ ω, (∫ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ B, g z.2 ∂(N.N ω)) ∂P) =
      (t : ℝ) * ∫ x in B, g x ∂ν := by
  sorry
end Kyprianou.Ch04
