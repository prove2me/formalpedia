-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionRawMarkedIntegralL1GivenFirstMomentV1
-- name    : Kyprianou.Ch02.prmFiniteRegionRawMarkedIntegralL1GivenFirstMomentV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T19:44:05.181038+00:00
-- url     : https://prove2.me/theorems/719614b9-ff6f-4721-baae-5a53b43d4423
-- title:
--   Finite-region KLS marked Poisson integrals are L1 under an integrable mark
-- statement:
--   The uncompensated finite-intensity marked Poisson integral has an integrable real-valued random variable at any bounded nonnegative time whenever the mark function identity is integrable against the restricted Levy measure. A signed Campbell formula, or a nonnegative Campbell bound for the absolute value, supplies the required integrable domination. This is the true stochastic L1 premise for the compensated integral and requires no square-integrability assumption.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.9, Poisson finite-band first moment estimate.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteRegionRawMarkedIntegralL1GivenFirstMomentV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hfirst : Integrable (fun x : ℝ => x) (ν.restrict B)) :
    ∀ t : ℝ≥0,
      Integrable (fun ω => ∫ z in
          (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) P
    := by sorry
