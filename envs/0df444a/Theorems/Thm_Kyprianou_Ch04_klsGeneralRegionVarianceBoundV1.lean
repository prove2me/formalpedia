-- Prove2me | Theorems.Thm_Kyprianou_Ch04_klsGeneralRegionVarianceBoundV1
-- name    : Kyprianou.Ch04.klsGeneralRegionVarianceBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:44:51.506832+00:00
-- url     : https://prove2.me/theorems/1ac966a7-4201-4744-bb9d-33cb9159fc23
-- title:
--   Finite-region real marked Poisson integral variance bound
-- statement:
--   The compensated real-mark integral over a finite-intensity time-mark window has integrable square, bounded by the time length times the restricted second moment of the intensity.
-- source:
--   Kyprianou (2006), Exercise 4.5(ii).

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Topology
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem klsGeneralRegionVarianceBoundV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν) (B : Set ℝ)
    (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (hsecond : MemLp (fun x : ℝ => x) 2 (ν.restrict B)) (t : ℝ≥0) :
    let D := fun ω => (∫ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ B, z.2 ∂(N.N ω)) -
        (t : ℝ) * ∫ x in B, x ∂ν
    Integrable (fun ω => (D ω)^2) P ∧
      (∫ ω, (D ω)^2 ∂P) ≤ (t : ℝ) * ∫ x in B, x^2 ∂ν := by
  sorry
end Kyprianou.Ch04
