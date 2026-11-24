-- Prove2me | Theorems.Thm_Kyprianou_Ch04_eventLocalizedPoissonKernel
-- name    : Kyprianou.Ch04.eventLocalizedPoissonKernel
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T22:01:54.484359+00:00
-- url     : https://prove2.me/theorems/698cc863-8cac-4773-a989-18cf649863c6
-- title:
--   Event and time localisation of admissible nonnegative Poisson kernels
-- statement:
--   Localise an admissible kernel by the event A at time u and by the left-continuous indicator of (u,t]. The resulting admissible kernel has both full-horizon integrals equal to the corresponding event-restricted increment integrals. This is a deterministic measurability, left-continuity and restriction identity, independent of compensation.
-- source:
--   Kyprianou (2006), Corollary 4.5, localisation reduction of 368c2a96-9778-4fa8-b48f-154c83796c1b

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

theorem Kyprianou.Ch04.eventLocalizedPoissonKernel
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (phi : Real -> Real -> Omega -> Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
    (u t : NNReal) (hut : u ≤ t)
    (A : Set Omega) (hA : MeasurableSet[F u] A) :
    ∃ psi : Real -> Real -> Omega -> Real,
      IsAdmissiblePoissonKernel P F psi ∧
      (∫⁻ omega,
        (∫⁻ z in Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ,
          ENNReal.ofReal (psi z.1 z.2 omega) ∂(N.N omega)) ∂P) =
      (∫⁻ omega in A,
        (∫⁻ z in Set.prod (Set.Ioc (u : Real) (t : Real)) Set.univ,
          ENNReal.ofReal (phi z.1 z.2 omega) ∂(N.N omega)) ∂P) ∧
      (∫⁻ omega,
        (∫⁻ s in Set.Icc (0 : Real) (t : Real),
          (∫⁻ x, ENNReal.ofReal (psi s x omega) ∂levyMeasure)
          ∂volume) ∂P) =
      (∫⁻ omega in A,
        (∫⁻ s in Set.Ioc (u : Real) (t : Real),
          (∫⁻ x, ENNReal.ofReal (phi s x omega) ∂levyMeasure)
          ∂volume) ∂P) := by sorry
