-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finiteRegionMarkedCharFromCountCharV2
-- name    : Kyprianou.Ch02.finiteRegionMarkedCharFromCountCharV2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T09:32:16.725323+00:00
-- url     : https://prove2.me/theorems/42cb0a36-72e3-46e3-b7dd-3b5317bb554b
-- title:
--   Lemma 2.8 raw marked-integral characteristic from count-characteristic laws
-- statement:
--   Given the explicit finite-window Poisson count characteristic law on each time window, establish the full marked-Poisson-integral characteristic exponent using the KLS PRM structure. This is the nontrivial marked-jump extension: apply disjoint count independence to finite simple mark profiles, then pass to the unbounded mark value via finite-activity almost-sure atoms and dominated convergence.
-- source:
--   Kyprianou Chapter 2 Lemma 2.8; exact Poisson/ProfileCharacter.lean and SimpleProfile.lean approach, single remaining marked-law bridge beyond count law.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem finiteRegionMarkedCharFromCountCharV2
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hCount : ∀ (t : ℝ≥0) (u : ℝ),
      ∫ ω, Complex.exp (Complex.I *
      ((u * (N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B)).toReal : ℝ) : ℂ)) ∂P =
    Complex.exp ((LevyStochCalc.Poisson.referenceIntensity ν
      (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B)).toReal *
      (Complex.exp (Complex.I * (u : ℂ)) - 1))) :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map
        (fun ω => ∫ z in
          (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω))) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in B,
          (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν) := by sorry
end Kyprianou.Ch02
