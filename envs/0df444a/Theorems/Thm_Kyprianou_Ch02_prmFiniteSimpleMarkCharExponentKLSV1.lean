-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteSimpleMarkCharExponentKLSV1
-- name    : Kyprianou.Ch02.prmFiniteSimpleMarkCharExponentKLSV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T18:34:42.154169+00:00
-- url     : https://prove2.me/theorems/010cf0da-266b-486f-b733-98fd6d9acbb1
-- title:
--   Finite-simple signed Poisson marked integral has exact characteristic exponent
-- statement:
--   For every finite real simple mark f, identify its signed marked Poisson integral with the finite weighted count sum (Proved prmFiniteSimpleMarkIntegralAEFibreSumKLSV1). Its disjoint cell counts are independent, Poisson distributed, and jointly stationary (Proved KLSFiniteVectorShiftCountLawV1 and N.independent_disjoint). Apply Poisson characteristic function to each count and independence to multiply exponentials. Identify the finite sum with the ν-integral of exp(iξ f(x))-1. Keep KLS provider throughout; avoid duplicate F000.
-- source:
--   Kyprianou (2006) Ch.2 Eq.2.3; Lévy–Khintchine finite-activity exponent.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteSimpleMarkCharExponentKLSV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ∀ (f : SimpleFunc ℝ ℝ) (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), f z.2 ∂(N.N ω))) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in B,
          (Complex.exp (Complex.I * (((ξ * f x : ℝ) : ℂ))) - 1) ∂ν) := by sorry
