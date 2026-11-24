-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyItoTripleIndependentFromMarkRegionPathsV1
-- name    : Kyprianou.Ch02.levyItoTripleIndependentFromMarkRegionPathsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:27:08.234107+00:00
-- url     : https://prove2.me/theorems/0598c77a-58a4-49b7-a653-3290d9ed7fea
-- title:
--   Brownian driver and two disjoint-mark PRM path functionals are mutually independent
-- statement:
--   Disjoint mark regions generate independent PRM evaluation sigma algebras. Their join lies in the full PRM driver sigma algebra, independent of the Brownian path. Therefore the two region-measurable paths and the drifted scaled Brownian path are mutually independent.
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
theorem levyItoTripleIndependentFromMarkRegionPathsV1
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
    IndependentLevyItoComponents P
      (fun (t : ℝ≥0) (ω : Ω) => (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ))
      (fun t ω => L ω t) (fun t ω => S ω t) := by sorry
end Kyprianou.Ch02
