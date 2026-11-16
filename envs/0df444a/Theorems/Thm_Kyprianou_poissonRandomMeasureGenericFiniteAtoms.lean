-- Prove2me | Theorems.Thm_Kyprianou_poissonRandomMeasureGenericFiniteAtoms
-- name    : Kyprianou.poissonRandomMeasureGenericFiniteAtoms
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T20:38:44.971357+00:00
-- url     : https://prove2.me/theorems/49100993-a7e9-4253-873b-6fd305b3b4aa
-- title:
--   Finite atoms of constructed Poisson random measure at finite total intensity
-- statement:
--   Finite atoms of constructed Poisson random measure at finite total intensity. This is an exact standalone conjunct of Kyprianou Chapter 2 support theorem, with all original quantified parameters and no additional hypotheses.
-- source:
--   Kyprianou (2006), Chapter 2 Poisson random measure support result, source-exact projection

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou
theorem poissonRandomMeasureGenericFiniteAtoms
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hfamily : ProbabilityTheory.IsPoissonPointFamily K Y m P) :
    (m Set.univ < ⊤ →
      ∀ᵐ ω ∂P,
        Set.Finite
          {z : E | ProbabilityTheory.poissonRandomMeasure K Y ω {z} ≠ 0})      := by sorry
end Kyprianou
