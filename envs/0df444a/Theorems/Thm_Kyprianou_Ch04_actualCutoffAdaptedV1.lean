-- Prove2me | Theorems.Thm_Kyprianou_Ch04_actualCutoffAdaptedV1
-- name    : Kyprianou.Ch04.actualCutoffAdaptedV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:22:24.242248+00:00
-- url     : https://prove2.me/theorems/5050f425-d871-41a9-8bbf-88395e2b133a
-- title:
--   Adaptedness of actual physical finite cutoff state
-- statement:
--   Both large and small marked jump integrals are measurable at time t because the filtration observes every measurable subset of the corresponding past region. The state is their sum with deterministic drift and compensator.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, physical cutoff processes.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem actualCutoffAdaptedV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hPast : ∀ (T : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Icc (0 : ℝ) (T : ℝ) ×ˢ univ →
      Measurable[F T] (fun ω => N.N ω D))
    (b a : ℝ) (Y X2 : NNReal → Ω → ℝ)
    (h2 : ∀ t ω, X2 t ω = b * (t : ℝ) +
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 ∂(N.N ω))
    (hY : ∀ t ω, Y t ω = X2 t ω +
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | a < |x| ∧ |x| < 1}, z.2 ∂(N.N ω)) -
      (t : ℝ) * ∫ x in {x : ℝ | a < |x| ∧ |x| < 1}, x ∂ν) :
    Adapted F Y := by
  sorry
end Kyprianou.Ch04
