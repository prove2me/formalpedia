-- Prove2me | Theorems.Thm_Kyprianou_Ch02_smallJumpCompactMarkSupportCapV1
-- name    : Kyprianou.Ch02.smallJumpCompactMarkSupportCapV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:49:33.539807+00:00
-- url     : https://prove2.me/theorems/7047d2b2-88ae-41ea-80e4-834e658906df
-- title:
--   A compact window has a strict upper bound on all small jump marks
-- statement:
--   The finite upper-half mark window is supported on finitely many points, so its largest absolute mark strictly below one is bounded away from one.
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

theorem Kyprianou.Ch02.smallJumpCompactMarkSupportCapV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (hν : ProbabilityTheory.IsLevyMeasure ν) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
      N.N ω (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | c < |x| ∧ |x| < 1}) = 0 := by sorry
