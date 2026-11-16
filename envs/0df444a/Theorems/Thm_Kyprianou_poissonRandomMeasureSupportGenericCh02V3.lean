-- Prove2me | Theorems.Thm_Kyprianou_poissonRandomMeasureSupportGenericCh02V3
-- name    : Kyprianou.poissonRandomMeasureSupportGenericCh02V3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T19:28:26.317737+00:00
-- url     : https://prove2.me/theorems/850b0bf8-217d-4310-a264-9e461e982efa
-- title:
--   Corollary 2.6: countable Poisson support on a general sigma-finite space
-- statement:
--   The atomic support of a Poisson random measure constructed from an independently marked point family is almost surely countable on a general sigma-finite measurable space, and finite when the intensity has finite total mass. This is the general statement of Corollary 2.6; the earlier real-valued Poisson support theorem remains a useful specialisation.
-- source:
--   Kyprianou (2006), Corollary 2.6, p. 40

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou
theorem poissonRandomMeasureSupportGenericCh02V3
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
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
