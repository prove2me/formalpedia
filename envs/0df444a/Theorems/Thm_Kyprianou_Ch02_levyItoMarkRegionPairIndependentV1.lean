-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyItoMarkRegionPairIndependentV1
-- name    : Kyprianou.Ch02.levyItoMarkRegionPairIndependentV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T22:42:57.449811+00:00
-- url     : https://prove2.me/theorems/a0218a1f-aa4a-4d07-8a2c-69c59b5168c5
-- title:
--   Brownian path independent of regional pair and disjoint mark paths independent
-- statement:
--   The Gaussian driver path is independent of the pair of large-mark and small-mark Poisson path functionals, and those two path functionals are independent.
-- source:
--   Kyprianou (2006), Chapter 2, decomposition of full-path independence

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

theorem Kyprianou.Ch02.levyItoMarkRegionPairIndependentV1
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (a : ℝ) (σ : ℝ≥0)
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (hDrivers : ProbabilityTheory.IndepFun
      (fun ω => fun (t : ℝ) => B.W t ω)
      (fun ω => N.N ω) P)
    (L S : Ω → ℝ≥0 → ℝ)
    (hL : Measurable[(⨆ C ∈ {C : Set (ℝ × ℝ) |
        C ⊆ ((Set.univ : Set ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}) ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)] L)
    (hS : Measurable[(⨆ C ∈ {C : Set (ℝ × ℝ) |
        C ⊆ ((Set.univ : Set ℝ) ×ˢ {x : ℝ | |x| < 1}) ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)] S) :
    IndepFun
      (fun (ω : Ω) (t : ℝ≥0) => (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ))
      (fun ω => (L ω, S ω)) P ∧ IndepFun L S P := by sorry
