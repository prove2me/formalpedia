-- Prove2me | Theorems.Thm_Kyprianou_poissonRandomMeasureSupportGenericMeasurableSingletons
-- name    : Kyprianou.poissonRandomMeasureSupportGenericMeasurableSingletons
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T07:50:16.204033+00:00
-- url     : https://prove2.me/theorems/8f6514a5-beca-4e41-bacc-0d1d3b2beb6b
-- title:
--   Corollary 2.6: countable and finite Poisson support, measurable singletons
-- statement:
--   The atomic support of a Poisson random measure constructed from an independently marked point family is almost surely countable on a general sigma-finite measurable space, and finite when the intensity has finite total mass. This is the general statement of Corollary 2.6; the earlier real-valued Poisson support theorem remains a useful specialisation. Corrected statement: singletons of the mark space E are assumed measurable (MeasurableSingletonClass E); this is necessary to identify positive singleton masses with observed Poisson atoms.
-- source:
--   Kyprianou (2006), Chapter 2, Corollary 2.6; corrected Lean measurable-space hypothesis

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou
theorem poissonRandomMeasureSupportGenericMeasurableSingletons
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSingletonClass E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hfamily : ProbabilityTheory.IsPoissonPointFamily K Y m P) :
    (∀ᵐ ω ∂P,
      Set.Countable
        {z : E | ProbabilityTheory.poissonRandomMeasure K Y ω {z} ≠ 0}) ∧
    (m Set.univ < ⊤ →
      ∀ᵐ ω ∂P,
        Set.Finite
          {z : E | ProbabilityTheory.poissonRandomMeasure K Y ω {z} ≠ 0})
      := by sorry
end Kyprianou
