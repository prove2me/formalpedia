-- Prove2me | Theorems.Thm_Kyprianou_poissonRandomMeasureSupportCountable
-- name    : Kyprianou.poissonRandomMeasureSupportCountable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T11:12:45.749204+00:00
-- url     : https://prove2.me/theorems/35423cc2-4e9e-49d2-bda5-bc02e7451c36
-- title:
--   Corollary 2.6: countable Poisson support and finite support at finite intensity
-- statement:
--   The support of the Poisson random measure is almost surely countable, and its restriction to each finite-intensity measurable set has almost surely finitely many atoms.
-- source:
--   Kyprianou (2006), Corollary 2.6, p. 40

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou
theorem poissonRandomMeasureSupportCountable
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure) :
    (∀ᵐ ω ∂P,
      Set.Countable {z : ℝ × ℝ | N.N ω {z} ≠ 0}) ∧
    ∀ (A : Set (ℝ × ℝ)), MeasurableSet A →
      LevyStochCalc.Poisson.referenceIntensity levyMeasure A < ⊤ →
      ∀ᵐ ω ∂P,
        Set.Finite {z : ℝ × ℝ | z ∈ A ∧ N.N ω {z} ≠ 0}
    := by sorry
end Kyprianou
