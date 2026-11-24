-- Prove2me | Theorems.Thm_Kyprianou_Ch04_eventCutoffIntensityIntegral
-- name    : Kyprianou.Ch04.eventCutoffIntensityIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:00:54.53706+00:00
-- url     : https://prove2.me/theorems/73cb0315-28a9-4e04-b15b-11346997fcbb
-- title:
--   The event and time cutoff transforms the full time-by-mark intensity integral into the restricted increment integral.
-- statement:
--   The event and time cutoff transforms the full time-by-mark intensity integral into the restricted increment integral.
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

theorem Kyprianou.Ch04.eventCutoffIntensityIntegral
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (phi : Real -> Real -> Omega -> Real)
    (u t : NNReal) (A : Set Omega) (hA : MeasurableSet A) :
    (∫⁻ omega, (∫⁻ s in Set.Icc (0 : Real) (t : Real),
      (∫⁻ x, ENNReal.ofReal (if (u : Real) < s ∧ omega ∈ A then phi s x omega else 0)
        ∂levyMeasure) ∂volume) ∂P) =
    (∫⁻ omega in A, (∫⁻ s in Set.Ioc (u : Real) (t : Real),
      (∫⁻ x, ENNReal.ofReal (phi s x omega) ∂levyMeasure) ∂volume) ∂P) := by sorry
