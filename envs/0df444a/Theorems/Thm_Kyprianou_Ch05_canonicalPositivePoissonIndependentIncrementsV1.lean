-- Prove2me | Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonIndependentIncrementsV1
-- name    : Kyprianou.Ch05.canonicalPositivePoissonIndependentIncrementsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:25:32.68881+00:00
-- url     : https://prove2.me/theorems/715f8644-1725-4a03-a4a7-4efcccf97e17
-- title:
--   Canonical positive Poisson integral with drift has independent increments
-- statement:
--   Disjoint adjacent strips have mutually independent evaluation sigma algebras by Chapter 2. Their mass functionals are measurable in those sigma algebras. Transfer independence to the actual increments using the simultaneous strip identity.
-- source:
--   Kyprianou (2006), Chapter 5, Theorem 5.6.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false

theorem Kyprianou.Ch05.canonicalPositivePoissonIndependentIncrementsV1
    {Lambda : Type} [MeasurableSpace Lambda]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) Q)
    (hint : Integrable (fun z : ℝ => min (1 : ℝ) |z|) Pi)
    (d : ℝ) :
    HasIndependentIncrements (fun (t : NNReal) (w : Lambda) =>
      d * (t : ℝ) + (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal) Q := by
  sorry
