-- Prove2me | Theorems.Thm_Kyprianou_Ch04_klsWindowIntegerValuedV1
-- name    : Kyprianou.Ch04.klsWindowIntegerValuedV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:09:18.092197+00:00
-- url     : https://prove2.me/theorems/d8a6dc39-71f5-4b2b-bab0-44ef593ce0cc
-- title:
--   KLS modular PRM finite natural windows are integer valued
-- statement:
--   On a single full probability event, a KLS modular Poisson random measure restricted to each finite natural time window and finite-intensity mark region is integer valued. Use the countable generating pi-system and generic integer-valued measure criterion without importing the conflicting F000 Poisson family.
-- source:
--   Kyprianou (2006), Exercise 4.5(i), and LevyStochCalc Poisson atomicity argument.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_SourceProof_adf2db00933ba5955625daf4
import Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F002
import Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F003
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson Filter Set
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem klsWindowIntegerValuedV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℕ,
      LevyStochCalc.Probability.IsIntegerValued
        ((N.N ω).restrict (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B)) := by
  sorry
end Kyprianou.Ch04
