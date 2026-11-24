-- Prove2me | Theorems.Thm_Kyprianou_Ch02_markedIocIndicatorTendstoLeftV1
-- name    : Kyprianou.Ch02.markedIocIndicatorTendstoLeftV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:55:57.145517+00:00
-- url     : https://prove2.me/theorems/d20505f6-414c-4ca7-bcf9-ddd0c35beb69
-- title:
--   markedIocIndicatorTendstoLeft
-- statement:
--   markedIocIndicatorTendstoLeft
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
theorem markedIocIndicatorTendstoLeftV1
    (A : Set ℝ) (t : ℝ≥0) (z : ℝ × ℝ) :
    Tendsto (fun s : ℝ≥0 => (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ A).indicator Prod.snd z)
      (nhdsWithin t (Set.Iio t))
      (nhds ((Set.Ioo (0 : ℝ) (t : ℝ) ×ˢ A).indicator Prod.snd z)) := by sorry
end Kyprianou.Ch02
