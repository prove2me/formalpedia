-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46WeakPassageSandwichV1
-- name    : Kyprianou.Ch04.exercise46WeakPassageSandwichV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:23:27.639224+00:00
-- url     : https://prove2.me/theorems/1051532f-d4e3-5111-9d0c-85224598d880
-- title:
--   Pathwise weak busy clock lies between strict passage clocks at neighbouring levels
-- statement:
--   Every weak crossing of the higher level is a strict crossing of the lower level, and every strict crossing of the higher level is a weak crossing. Compare the three infima.
-- source:
--   Kyprianou (2006), Exercise 4.6(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46WeakPassageSandwichV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (x y : Real) (hxy : x < y) (w : Omega) :
    let B : WithTop NNReal :=
      sInf {v : WithTop NNReal |
        ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ y ≤ L.X t w}
    Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w ≤ B ∧
      B ≤ Kyprianou.Ch03.firstHittingTime L.X (Ioi y) w := by
  sorry
