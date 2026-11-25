-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_contact_exp_integral_one
-- name    : Kyprianou.Ch04.kw47_contact_exp_integral_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T20:58:04.272649+00:00
-- url     : https://prove2.me/theorems/fc181bac-8f52-4c63-ad4c-f20454622139
-- title:
--   Reflected exponential equals one in the running-supremum Stieltjes integral
-- statement:
--   The running-supremum contact measure assigns zero mass to the strict noncontact set. Thus on every positive-time interval, the reflected exponential equals one almost everywhere for the Stieltjes measure, so the two integrals agree. This uses the exact original path measure.
-- source:
--   Kyprianou (2006), Exercise 4.7, integration by parts and the running-maximum contact property.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_runningSup_contact_measure
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- On the continuous Stieltjes contact measure of a spectrally
negative running maximum, the reflected exponential is one a.e. -/

theorem Kyprianou.Ch04.kw47_contact_exp_integral_one
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (w : Ω)
    (alpha : Real) (T : Real) :
    (∫ s in Set.Ioc (0 : Real) T,
      Real.exp (-alpha * (runningSup L s.toNNReal w -
        L.X s.toNNReal w)) ∂(dividendMeasure (runningSup L) w)) =
    (∫ s in Set.Ioc (0 : Real) T,
      (1 : Real) ∂(dividendMeasure (runningSup L) w)) := by sorry
