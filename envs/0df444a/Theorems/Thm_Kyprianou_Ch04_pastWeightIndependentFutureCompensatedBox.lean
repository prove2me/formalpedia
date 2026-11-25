-- Prove2me | Theorems.Thm_Kyprianou_Ch04_pastWeightIndependentFutureCompensatedBox
-- name    : Kyprianou.Ch04.pastWeightIndependentFutureCompensatedBox
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T18:59:57.969795+00:00
-- url     : https://prove2.me/theorems/a59afc92-89fe-579e-b29f-4a2c5d555b83
-- title:
--   Past random weights are independent of future compensated Poisson boxes
-- statement:
--   Under the Chapter 4 future-independence hypothesis, every F_u-measurable real weight is independent of the compensated count of the Poisson random measure on a measurable mark region during the future time interval (u,t]. The conclusion is exact independence of the random variables and does not require finite mark intensity because it concerns measurability and independence only.
-- source:
--   Kyprianou (2006) Chapter 4, predictable jump compensation/isometry: direct independence consequence of the current formal IsFutureIndependentPoissonMeasure hypothesis; split-source LevyStochCalc past compensated box argument adapted to the correct NNReal filtration.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Future compensated-box counts are independent of scalar weights measurable in the past. -/

theorem Kyprianou.Ch04.pastWeightIndependentFutureCompensatedBox
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure Real) [SigmaFinite nu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P nu)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P nu F N)
    (u t : NNReal) (hut : u ≤ t)
    (B : Set Real) (hB : MeasurableSet B)
    (f : Omega → Real)
    (hf : @StronglyMeasurable Omega Real _ (F u) f) :
    IndepFun f (fun omega => N.compensated (Set.Ioc (u : Real) (t : Real) ×ˢ B) omega) P := by
  sorry
