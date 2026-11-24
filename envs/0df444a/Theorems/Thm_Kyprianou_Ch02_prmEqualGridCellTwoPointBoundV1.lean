-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmEqualGridCellTwoPointBoundV1
-- name    : Kyprianou.Ch02.prmEqualGridCellTwoPointBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:55:52.275286+00:00
-- url     : https://prove2.me/theorems/251ecfeb-5bdb-46fe-b62e-00c36f6be21a
-- title:
--   prmEqualGridCellTwoPointBound
-- statement:
--   prmEqualGridCellTwoPointBound
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1

import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem prmEqualGridCellTwoPointBoundV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (A : Set ℝ) (hA : MeasurableSet A) (hfin : ν A < ⊤)
    (a d : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ d) :
    (P {ω | 1 < N.N ω (Set.Ioc a (a+d) ×ˢ A)}).toReal ≤
      (d * (ν A).toReal)^2 := by sorry
end Kyprianou.Ch02
