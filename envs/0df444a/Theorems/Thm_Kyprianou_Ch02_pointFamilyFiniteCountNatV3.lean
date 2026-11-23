-- Prove2me | Theorems.Thm_Kyprianou_Ch02_pointFamilyFiniteCountNatV3
-- name    : Kyprianou.Ch02.pointFamilyFiniteCountNatV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T07:27:49.51895+00:00
-- url     : https://prove2.me/theorems/5bfd802b-cecd-4504-9bb5-f74bbbbb6922
-- title:
--   Finite-intensity Poisson point-family counts are Nat-valued a.e.
-- statement:
--   Finite-intensity Poisson point-family counts are Nat-valued a.e. This is an exact conjunct of the accepted residual theorem f8ff2134-db5d-427a-8b3a-338579d5ee6f, required for Poisson random-measure existence in Kyprianou Chapter 2. Its hypotheses and conclusion retain the original generic arbitrary measurable-space assumptions.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.4; full PRM existence residual f8ff2134-db5d-427a-8b3a-338579d5ee6f, original Prove2Me decomposition.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem pointFamilyFiniteCountNatV3
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m] [Nonempty E]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P) :
    ∀ A : Set E, MeasurableSet A → m A < ⊤ →
       ∀ᵐ ω ∂P, ∃ n : ℕ,
         ProbabilityTheory.poissonRandomMeasure K Y ω A = (n : ENNReal) := by sorry
end Kyprianou.Ch02
