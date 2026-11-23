-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionCharExponentV1
-- name    : Kyprianou.Ch02.prmFiniteRegionCharExponentV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T08:55:58.800047+00:00
-- url     : https://prove2.me/theorems/349fad56-7134-48e1-8908-23c88fd1b279
-- title:
--   Compound-Poisson characteristic exponent of a finite-region stochastic integral
-- statement:
--   Derive the finite-region Laplace/characteristic functional from the Poisson random-measure laws, including the zero-intensity case and unbounded marks on a finite-rate region.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.8, finite-region Poisson integral; sound decomposition of the Chapter 2 theorem Kyprianou.finiteRegionPoissonIntegralCh02V3 (38df877c-0872-40d5-8b33-bbad3487ba47), itself already linked to Kyprianou.largeJumpProcessLevy (5c06d985-05f1-4c04-aa68-fc6de328bbfa).

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteRegionCharExponentV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω))) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in B,
          (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν) := by sorry
