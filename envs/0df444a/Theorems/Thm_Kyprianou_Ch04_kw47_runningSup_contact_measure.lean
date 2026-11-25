-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_runningSup_contact_measure
-- name    : Kyprianou.Ch04.kw47_runningSup_contact_measure
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T08:41:18.695428+00:00
-- url     : https://prove2.me/theorems/fd4e7cdc-13ed-4a9c-a364-90f4492370fe
-- title:
--   Running-supremum Stieltjes measure is carried by contact
-- statement:
--   Spectral negativity implies continuous running supremum and hence atomless dividend measure. Positive drawdown implies a right interval on which the running supremum is constant. Its Stieltjes mass is zero, so the noncontact set has zero mass.
-- source:
--   Kyprianou (2006), Exercise 4.7, pp. 320-321; continuous Stieltjes product calculus.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_no_real_atoms
import Theorems.Thm_AvramDividend_Classical_runningSup_right_local_const_of_positive_drawdown
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_runningSup_contact_measure
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : SpectrallyNegativeLevy P F) (w : Omega) :
    (dividendMeasure (runningSup L) w)
      {s : Real | 0 ≤ s ∧ L.X s.toNNReal w < runningSup L s.toNNReal w} = 0 := by sorry
