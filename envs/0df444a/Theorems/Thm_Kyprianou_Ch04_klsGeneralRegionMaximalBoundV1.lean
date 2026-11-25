-- Prove2me | Theorems.Thm_Kyprianou_Ch04_klsGeneralRegionMaximalBoundV1
-- name    : Kyprianou.Ch04.klsGeneralRegionMaximalBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:46:29.014927+00:00
-- url     : https://prove2.me/theorems/25d39c94-ec01-5b4e-8da4-d1213d8d6542
-- title:
--   Finite-region compensated Poisson integral maximal L2 bound
-- statement:
--   The maximal squared compensated real-mark integral over a finite intensity region is integrable and its expectation is at most four times the time horizon times the restricted intensity second moment.
-- source:
--   Kyprianou (2006), Exercise 4.5(ii).

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Topology
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem klsGeneralRegionMaximalBoundV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν) (B : Set ℝ)
    (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (hsecond : MemLp (fun x : ℝ => x) 2 (ν.restrict B))
    (T : ℝ≥0) (hT : 0 < T) :
    let D := fun (t : ℝ≥0) ω => (∫ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ B, z.2 ∂(N.N ω)) -
        (t : ℝ) * ∫ x in B, x ∂ν
    Integrable (fun ω => sSup ((fun t : ℝ≥0 => |D t ω|^2) '' Iic T)) P ∧
      (∫ ω, sSup ((fun t : ℝ≥0 => |D t ω|^2) '' Iic T) ∂P) ≤
        4 * (T : ℝ) * ∫ x in B, x^2 ∂ν := by
  sorry
end Kyprianou.Ch04
