-- Prove2me | Theorems.Thm_Kyprianou_Ch02_largeJumpPathMeasurableMarkRegionV1
-- name    : Kyprianou.Ch02.largeJumpPathMeasurableMarkRegionV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:27:07.7388+00:00
-- url     : https://prove2.me/theorems/efb96274-1bf0-492f-8dc2-9a546110e86b
-- title:
--   The large-jump path is measurable in the large-mark PRM evaluation sigma algebra
-- statement:
--   Each time evaluation is a marked integral on a subregion of the large-mark region. Its measurability relative to the region evaluation sigma algebra implies measurable full path.
-- source:
--   Kyprianou (2006), Theorem 2.1; independence of the three Lévy–Itô components

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

namespace Kyprianou.Ch02
theorem largeJumpPathMeasurableMarkRegionV1
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
 :
    Measurable[(⨆ C ∈ {C : Set (ℝ × ℝ) |
        C ⊆ ((Set.univ : Set ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}) ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)]
      (fun ω => fun t : ℝ≥0 => Kyprianou.largeJumpProcess P levyMeasure N t ω) := by sorry
end Kyprianou.Ch02
