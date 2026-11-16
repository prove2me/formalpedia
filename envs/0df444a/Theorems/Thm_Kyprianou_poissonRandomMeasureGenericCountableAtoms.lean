-- Prove2me | Theorems.Thm_Kyprianou_poissonRandomMeasureGenericCountableAtoms
-- name    : Kyprianou.poissonRandomMeasureGenericCountableAtoms
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T20:38:46.376473+00:00
-- url     : https://prove2.me/theorems/b9b1d763-c3e8-43dd-8b22-ab1f33cb08c4
-- title:
--   Countable atoms of constructed Poisson random measure
-- statement:
--   Countable atoms of constructed Poisson random measure. This is an exact standalone conjunct of Kyprianou Chapter 2 support theorem, with all original quantified parameters and no additional hypotheses.
-- source:
--   Kyprianou (2006), Chapter 2 Poisson random measure support result, source-exact projection

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou
theorem poissonRandomMeasureGenericCountableAtoms
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hfamily : ProbabilityTheory.IsPoissonPointFamily K Y m P) :
    (∀ᵐ ω ∂P,
      Set.Countable
        {z : E | ProbabilityTheory.poissonRandomMeasure K Y ω {z} ≠ 0})      := by sorry
end Kyprianou
