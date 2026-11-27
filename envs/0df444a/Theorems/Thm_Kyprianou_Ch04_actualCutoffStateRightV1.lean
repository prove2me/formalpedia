-- Prove2me | Theorems.Thm_Kyprianou_Ch04_actualCutoffStateRightV1
-- name    : Kyprianou.Ch04.actualCutoffStateRightV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:14:04.15539+00:00
-- url     : https://prove2.me/theorems/25083039-f629-473f-874b-ab21f0363d38
-- title:
--   actualCutoffStateRightV1
-- statement:
--   actualCutoffStateRightV1
-- source:
--   Kyprianou (2006), Exercise 4.5(iii)

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionCadlagAEV1
import Theorems.Thm_Kyprianou_Ch04_zeroTimeRestrictionIccIocV1
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A finite retained-band state is right continuous on the same physical sample
space, without a first-moment assumption on its large marks. -/

theorem Kyprianou.Ch04.actualCutoffStateRightV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (Y X2 : NNReal → Ω → ℝ) (b a : ℝ) (ha : 0 < a)
    (hz : ∀ᵐ w ∂P, N.N w (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0)
    (h2 : ∀ t w, X2 t w = b * (t : ℝ) +
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 ∂(N.N w))
    (hY : ∀ t w, Y t w = X2 t w +
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | a < |x| ∧ |x| < 1},
        z.2 ∂(N.N w)) - (t : ℝ) * ∫ x in {x : ℝ | a < |x| ∧ |x| < 1}, x ∂ν) :
    ∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun s => Y s w) (Ici t) t := by
  sorry
