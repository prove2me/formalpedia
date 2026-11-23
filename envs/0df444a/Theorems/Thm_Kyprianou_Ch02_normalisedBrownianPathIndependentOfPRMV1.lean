-- Prove2me | Theorems.Thm_Kyprianou_Ch02_normalisedBrownianPathIndependentOfPRMV1
-- name    : Kyprianou.Ch02.normalisedBrownianPathIndependentOfPRMV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T21:37:32.391055+00:00
-- url     : https://prove2.me/theorems/6b9ecd4a-3e29-4c5d-b088-71c3cb09d6a9
-- title:
--   Independence of Poisson random measure from origin-centred Brownian paths
-- statement:
--   If the entire Brownian path B.W is independent of the PRM N.N, then their composed measurable path functional t↦B.Wt−B.W0 is also independent of N.N. Use the pinned Mathlib ProbabilityTheory.IndepFun.comp theorem and the measurable Pi-space map φ(f)(t)=f(t)−f(0). This is a short, self-contained proof about measurable composition and requires no Brownian distributional properties.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1: normalised independent driving Brownian motion.

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

theorem normalisedBrownianPathIndependentOfPRMV1
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (hDrivers : ProbabilityTheory.IndepFun
      (fun ω => fun (t : ℝ) => B.W t ω)
      (fun ω => N.N ω) P) :
    ProbabilityTheory.IndepFun
      (fun ω => fun (t : ℝ) => B.W t ω - B.W 0 ω)
      (fun ω => N.N ω) P := by sorry

end Kyprianou.Ch02
