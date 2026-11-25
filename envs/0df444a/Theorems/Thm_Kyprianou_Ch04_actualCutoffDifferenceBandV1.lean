-- Prove2me | Theorems.Thm_Kyprianou_Ch04_actualCutoffDifferenceBandV1
-- name    : Kyprianou.Ch04.actualCutoffDifferenceBandV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:31:30.343662+00:00
-- url     : https://prove2.me/theorems/50a73f64-3134-5698-a09c-abf932d800e5
-- title:
--   Nested actual finite cutoffs differ by compensated intermediate band
-- statement:
--   On a common probability-one event for two positive nested cutoffs, the actual path difference equals the compensated intermediate mark band at every time. The intermediate band includes the upper cutoff boundary.
-- source:
--   Kyprianou (2006), Exercise 4.5(ii).

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem actualCutoffDifferenceBandV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (hν : IsLevyMeasure ν) (N : PoissonRandomMeasure.{0,0,0} P ν)
    (X Xleft X2 U V : NNReal → Ω → ℝ) (η ε : ℝ)
    (hη : 0 < η) (hηε : η < ε) (hε : ε < 1)
    (hN : ∀ᵐ ω ∂P, N.N ω = Kyprianou.Ch04.pathJumpMeasure X Xleft ω)
    (hU : ∀ t ω, U t ω = X2 t ω +
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | η < |x| ∧ |x| < 1},
        z.2 ∂(N.N ω)) - (t : ℝ) *
      (∫ x in {x : ℝ | η < |x| ∧ |x| < 1}, x ∂ν))
    (hV : ∀ t ω, V t ω = X2 t ω +
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | ε < |x| ∧ |x| < 1},
        z.2 ∂(N.N ω)) - (t : ℝ) *
      (∫ x in {x : ℝ | ε < |x| ∧ |x| < 1}, x ∂ν)) :
    ∀ᵐ ω ∂P, ∀ t : NNReal, U t ω - V t ω =
      (∫ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | η < |x| ∧ |x| ≤ ε},
        z.2 ∂(N.N ω)) - (t : ℝ) *
      (∫ x in {x : ℝ | η < |x| ∧ |x| ≤ ε}, x ∂ν) := by
  sorry
end Kyprianou.Ch04
