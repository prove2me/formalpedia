-- Prove2me | Theorems.Thm_Kyprianou_Ch04_eventCutoffRawIntegral
-- name    : Kyprianou.Ch04.eventCutoffRawIntegral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T23:00:34.299346+00:00
-- url     : https://prove2.me/theorems/0ae5b386-fb65-4634-b92b-1d061df571b7
-- title:
--   The event and time cutoff transforms the full raw nonnegative random-measure integral into the restricted increment integral.
-- statement:
--   The event and time cutoff transforms the full raw nonnegative random-measure integral into the restricted increment integral.
-- source:
--   Kyprianou (2006), Corollary 4.5, corrected common-null formulation bf5da7d2-0e15-44ab-8e4a-28f5a74879e6

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Classical

theorem Kyprianou.Ch04.eventCutoffRawIntegral
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (phi : Real -> Real -> Omega -> Real)
    (u t : NNReal) (A : Set Omega) (hA : MeasurableSet A) :
    (∫⁻ omega, (∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
      ENNReal.ofReal (if (u : Real) < z.1 ∧ omega ∈ A then phi z.1 z.2 omega else 0)
      ∂(N.N omega)) ∂P) =
    (∫⁻ omega in A, (∫⁻ z in Set.Ioc (u : Real) (t : Real) ×ˢ Set.univ,
      ENNReal.ofReal (phi z.1 z.2 omega) ∂(N.N omega)) ∂P) := by sorry
