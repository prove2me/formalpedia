-- Prove2me | Theorems.Thm_Kyprianou_Ch04_actualCutoffAffineStepsV1
-- name    : Kyprianou.Ch04.actualCutoffAffineStepsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:19:39.00935+00:00
-- url     : https://prove2.me/theorems/7005a7b9-64ee-4f49-8438-bfdb93ced37d
-- title:
--   Actual finite-cutoff paths have effective drift and finite steps
-- statement:
--   With an intrinsic path-jump law, the actual finite-cutoff path and large-jump process admit simultaneous affine plus finite-step representations on every compact horizon, with effective drift equal to the Lévy drift minus the strict small-band first moment.
-- source:
--   Kyprianou (2006), Exercise 4.5(i).

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem actualCutoffAffineStepsV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (hν : IsLevyMeasure ν) (N : PoissonRandomMeasure.{0,0,0} P ν)
    (X Xleft X2 Y : NNReal → Ω → ℝ) (b ε : ℝ) (hε : 0 < ε)
    (hN : ∀ᵐ ω ∂P, N.N ω = Kyprianou.Ch04.pathJumpMeasure X Xleft ω)
    (h2 : ∀ t ω, X2 t ω = b * (t : ℝ) +
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 ∂(N.N ω))
    (hY : ∀ t ω, Y t ω = X2 t ω +
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | ε < |x| ∧ |x| < 1},
        z.2 ∂(N.N ω)) -
      (t : ℝ) * (∫ x in {x : ℝ | ε < |x| ∧ |x| < 1}, x ∂ν)) :
    ∀ᵐ ω ∂P, ∀ T : ℕ,
      ∃ (L S : Finset (ℝ × ℝ)) (a c : ℝ × ℝ → ℝ),
        ∀ t : NNReal, t ≤ (T : NNReal) →
          X2 t ω = b * (t : ℝ) + (∑ p ∈ L, if p.1 ≤ (t : ℝ) then a p else 0) ∧
          Y t ω = (b - ∫ x in {x : ℝ | ε < |x| ∧ |x| < 1}, x ∂ν) * (t : ℝ) +
            (∑ p ∈ L, if p.1 ≤ (t : ℝ) then a p else 0) +
            (∑ p ∈ S, if p.1 ≤ (t : ℝ) then c p else 0) := by
  sorry
end Kyprianou.Ch04
