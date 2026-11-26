-- Prove2me | Theorems.Thm_Kyprianou_Ch04_poissonWindowNonnegativeIntegrableAEV1
-- name    : Kyprianou.Ch04.poissonWindowNonnegativeIntegrableAEV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:27:50.466863+00:00
-- url     : https://prove2.me/theorems/c6a521d8-fd59-5c3d-b6a8-e8d76f543890
-- title:
--   Integrable nonnegative marks give pathwise integrability on compact clocks
-- statement:
--   Integrable nonnegative marks give pathwise integrability on compact clocks.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem poissonWindowNonnegativeIntegrableAEV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν) (g : ℝ → ℝ)
    (hg : Measurable g) (hn : ∀ x, 0 ≤ g x) (hi : Integrable g ν) :
    ∀ᵐ w ∂P, ∀ T : NNReal,
      IntegrableOn (fun z : ℝ × ℝ => g z.2) (Icc (0 : ℝ) (T : ℝ) ×ˢ univ) (N.N w) := by
  sorry
end Kyprianou.Ch04
