-- Prove2me | Theorems.Thm_Kyprianou_Ch02_smallJumpTimeSliceIntegralBoundV1
-- name    : Kyprianou.Ch02.smallJumpTimeSliceIntegralBoundV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T22:49:32.003457+00:00
-- url     : https://prove2.me/theorems/4a06fea4-2184-4496-bd73-8a58bc089068
-- title:
--   A one-count time slice supported on marks below c has integral bounded by c
-- statement:
--   The restricted measure has mass at most one and the norm of the mark is at most c almost everywhere. Apply the bounded-integral norm estimate.
-- source:
--   Kyprianou (2006), Chapter 2, strict jump cap in Lévy-Itô decomposition

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

open scoped Topology

open Kyprianou Kyprianou.Ch02

theorem Kyprianou.Ch02.smallJumpTimeSliceIntegralBoundV1
    (μ : Measure (ℝ × ℝ)) (t e c : ℝ) (hc : 0 ≤ c)
    (hcount : μ ({t} ×ˢ {x : ℝ | e ≤ |x| ∧ |x| < 1}) ≤ 1)
    (hcap : μ ({t} ×ˢ {x : ℝ | c < |x| ∧ |x| < 1}) = 0) :
    |∫ z in ({t} ×ˢ {x : ℝ | e ≤ |x| ∧ |x| < 1}), z.2 ∂μ| ≤ c := by sorry
