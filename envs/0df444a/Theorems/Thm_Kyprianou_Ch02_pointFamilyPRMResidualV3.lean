-- Prove2me | Theorems.Thm_Kyprianou_Ch02_pointFamilyPRMResidualV3
-- name    : Kyprianou.Ch02.pointFamilyPRMResidualV3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T07:14:16.208485+00:00
-- url     : https://prove2.me/theorems/f8ff2134-db5d-427a-8b3a-338579d5ee6f
-- title:
--   Remaining genuine generic point-family PRM count laws
-- statement:
--   The concrete point-family PRM is a random counting measure with natural-or-infinity counts on all finite and infinite measurable regions, and its measurable count evaluations on arbitrary countable disjoint families are mutually independent. This collects exactly the three mathematically nontrivial gaps to be proved after the already Proved finite-region bridge.
-- source:
--   Kyprianou (2006) Chapter 2 original theorem 2.4; source-faithful decomposition of V3 canonical UUID 608b5f9b-92ff-404c-84cf-b60b94d76971; LeanLevy Poisson point-family existence and construction.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem pointFamilyPRMResidualV3
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m] [Nonempty E]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P) :
    (∀ A : Set E, MeasurableSet A → m A < ⊤ →
       ∀ᵐ ω ∂P, ∃ n : ℕ, ProbabilityTheory.poissonRandomMeasure K Y ω A = (n : ENNReal)) ∧
    (∀ A : Set E, MeasurableSet A → m A = ⊤ →
       ∀ᵐ ω ∂P, ProbabilityTheory.poissonRandomMeasure K Y ω A = ⊤) ∧
    (∀ {ι : Type} [Countable ι] (A : ι → Set E),
       (∀ i, MeasurableSet (A i)) →
       Pairwise (fun i j => Disjoint (A i) (A j)) →
       ProbabilityTheory.iIndepFun
         (fun i (ω : Ω) => ProbabilityTheory.poissonRandomMeasure K Y ω (A i)) P) := by sorry
end Kyprianou.Ch02
