-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finiteRegionPRMSimpleTimeSlicesV1
-- name    : Kyprianou.Ch02.finiteRegionPRMSimpleTimeSlicesV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T22:49:39.162784+00:00
-- url     : https://prove2.me/theorems/1e6a537c-8273-4b74-be0a-88882a42de7a
-- title:
--   Finite-mark Poisson random measures have at most one atom per time
-- statement:
--   The finite-rate count process has simple time atoms almost surely. Countably many uniform grids have probabilities of any two-count cell tending to zero. Each positive time belongs to some cell in every grid.
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

theorem Kyprianou.Ch02.finiteRegionPRMSimpleTimeSlicesV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t ≤ T →
      N.N ω ({(t : ℝ)} ×ˢ B) ≤ 1 := by sorry
