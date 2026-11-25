-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteCutoffWindowStepsV1
-- name    : Kyprianou.Ch04.finiteCutoffWindowStepsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T21:09:18.021499+00:00
-- url     : https://prove2.me/theorems/39591490-c342-44aa-80ab-a10a1b3fcc31
-- title:
--   Pure-jump finite cutoff: simultaneous large and small jump step paths
-- statement:
--   For every positive cutoff, on one probability-one event and each natural compact horizon, the large-jump and finite small-band raw marked integrals are finite step functions. Both representations use the same path and are valid at every time in the window. Adding the compensated linear drift gives the finite-cutoff path representation for Exercise 4.5(i).
-- source:
--   Kyprianou (2006), Exercise 4.5(i); finite-intensity PRM atomicity and step representation.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Simultaneous finite step representations on all compact windows. -/
theorem finiteCutoffWindowStepsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ T : ℕ,
      ∃ (large small : Finset (ℝ × ℝ)) (a c : ℝ × ℝ → ℝ),
        ∀ t : NNReal, t ≤ (T : NNReal) →
          (∫ z in (Ioc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}),
            z.2 ∂(N.N ω)) = (∑ p ∈ large, if p.1 ≤ (t : ℝ) then a p else 0) ∧
          (∫ z in (Ioc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | ε < |x| ∧ |x| < 1}),
            z.2 ∂(N.N ω)) = (∑ p ∈ small, if p.1 ≤ (t : ℝ) then c p else 0) := by
  sorry
end Kyprianou.Ch04
