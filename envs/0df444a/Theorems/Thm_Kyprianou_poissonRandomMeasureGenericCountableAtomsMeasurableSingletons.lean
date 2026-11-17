-- Prove2me | Theorems.Thm_Kyprianou_poissonRandomMeasureGenericCountableAtomsMeasurableSingletons
-- name    : Kyprianou.poissonRandomMeasureGenericCountableAtomsMeasurableSingletons
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T07:50:23.674538+00:00
-- url     : https://prove2.me/theorems/3b09e9e8-6238-4997-859a-334e30b7d5d5
-- title:
--   Countable atoms of a Poisson random measure with measurable singletons
-- statement:
--   Countable atoms of constructed Poisson random measure. This is an exact standalone conjunct of Kyprianou Chapter 2 support theorem, with all original quantified parameters and no additional hypotheses. Corrected statement: singletons of the mark space E are assumed measurable (MeasurableSingletonClass E); this is necessary to identify positive singleton masses with observed Poisson atoms.
-- source:
--   Kyprianou (2006), Chapter 2, Corollary 2.6; corrected Lean measurable-space hypothesis

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou
theorem poissonRandomMeasureGenericCountableAtomsMeasurableSingletons
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSingletonClass E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hfamily : ProbabilityTheory.IsPoissonPointFamily K Y m P) :
    (∀ᵐ ω ∂P,
      Set.Countable
        {z : E | ProbabilityTheory.poissonRandomMeasure K Y ω {z} ≠ 0})      := by sorry
end Kyprianou
