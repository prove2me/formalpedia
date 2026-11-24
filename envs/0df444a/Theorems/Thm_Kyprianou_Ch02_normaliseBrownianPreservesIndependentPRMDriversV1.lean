-- Prove2me | Theorems.Thm_Kyprianou_Ch02_normaliseBrownianPreservesIndependentPRMDriversV1
-- name    : Kyprianou.Ch02.normaliseBrownianPreservesIndependentPRMDriversV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T21:34:13.877811+00:00
-- url     : https://prove2.me/theorems/6a007816-f4d4-4e09-8996-7a40c9a59266
-- title:
--   Pointwise Brownian origin normalisation preserves the Brownian and independent Poisson driver structure
-- statement:
--   For a KLS BrownianMotion B on a fixed probability space and an independent Poisson random measure N, define Wprime(t,omega)=B.W(t,omega)-B.W(0,omega) for every path and time. Prove this defines another BrownianMotion P: measurability and joint measurability follow by subtraction, Gaussian increments are unchanged, continuity and negative-time support persist almost surely, and joint past-future independence follows since the normalised past filtration is contained in the original past filtration while increments agree. Independence of Wprime and N follows because Wprime is a measurable functional of the full original Brownian path. Crucially Wprime(0,omega)=0 for every omega, repairing the formally Disproved unrestricted sourceFaithfulLevyItoComponentsFromDriversV1 theorem.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1, pointwise normalisation of Brownian driver under independent Poisson coupling.

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

theorem normaliseBrownianPreservesIndependentPRMDriversV1
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (hDrivers : ProbabilityTheory.IndepFun
      (fun ω => fun (t : ℝ) => B.W t ω)
      (fun ω => N.N ω) P) :
    ∃ B' : LevyStochCalc.Brownian.BrownianMotion P,
      (∀ (t : ℝ) (ω : Ω), B'.W t ω = B.W t ω - B.W 0 ω) ∧
      (∀ ω : Ω, B'.W 0 ω = 0) ∧
      ProbabilityTheory.IndepFun
        (fun ω => fun (t : ℝ) => B'.W t ω)
        (fun ω => N.N ω) P := by sorry

end Kyprianou.Ch02
