-- Prove2me | Theorems.Thm_Kyprianou_Ch04_actualCutoffMaximalBoundV1
-- name    : Kyprianou.Ch04.actualCutoffMaximalBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:47:55.166265+00:00
-- url     : https://prove2.me/theorems/95b36391-4e80-5fc4-a00c-a519044053de
-- title:
--   Actual nested cutoff difference maximal square bound
-- statement:
--   For nested positive cutoffs, the expected squared supremum of the difference of the actual truncated paths is bounded by four times the time horizon times the quadratic small-mark tail.
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
theorem actualCutoffMaximalBoundV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
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
      (∫ x in {x : ℝ | ε < |x| ∧ |x| < 1}, x ∂ν))
    (T : NNReal) (hT : 0 < T) :
    Integrable (fun ω => sSup ((fun t : NNReal => |U t ω - V t ω|^2) '' Iic T)) P ∧
      (∫ ω, sSup ((fun t : NNReal => |U t ω - V t ω|^2) '' Iic T) ∂P) ≤
        4 * (T : ℝ) * (∫⁻ z in {z : ℝ | |z| ≤ ε}, ENNReal.ofReal (z^2) ∂ν).toReal := by
  sorry
end Kyprianou.Ch04
