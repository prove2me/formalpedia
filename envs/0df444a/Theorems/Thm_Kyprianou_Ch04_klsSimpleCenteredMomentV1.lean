-- Prove2me | Theorems.Thm_Kyprianou_Ch04_klsSimpleCenteredMomentV1
-- name    : Kyprianou.Ch04.klsSimpleCenteredMomentV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:42:11.52616+00:00
-- url     : https://prove2.me/theorems/2d554b98-9f1d-4315-8f99-6f35003a7db3
-- title:
--   Exact variance of a signed simple marked Poisson integral
-- statement:
--   The centred finite signed simple-mark Poisson integral has integrable square and its second moment equals time multiplied by the intensity integral of the squared mark.
-- source:
--   Kyprianou (2006), Exercise 4.5(ii).

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem klsSimpleCenteredMomentV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν) (B : Set ℝ)
    (hB : MeasurableSet B) (hfinite : ν B < ⊤) (g : SimpleFunc ℝ ℝ) (t : ℝ≥0) :
    let D := fun ω => (∫ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ B, g z.2 ∂(N.N ω)) -
        (t : ℝ) * ∫ x in B, g x ∂ν
    Integrable (fun ω => (D ω)^2) P ∧
      (∫ ω, (D ω)^2 ∂P) = (t : ℝ) * ∫ x in B, (g x)^2 ∂ν := by
  sorry
end Kyprianou.Ch04
