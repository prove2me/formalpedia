-- Prove2me | Theorems.Thm_OAI_Kadison_TracialSequence_projection_rep_lift
-- name    : OAI.Kadison.TracialSequence.projection_rep_lift
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:46:09.473677+00:00
-- url     : https://prove2.me/theorems/d7ea35ee-003b-4b32-83de-7b78c486552c
-- title:
--   OAI.Kadison.TracialSequence.projection_rep_lift: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialSequence`, with `open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder`, `open Filter UniformSpace Completion`, `open TracialGNS HilbertSequence`):
--
--   ```lean
--   lemma projection_rep_lift {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
--       [CompleteSpace G] (N : VonNeumannAlgebra G) (f : N →⋆ₐ[ℂ] A)
--       {e : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω}
--       (he : IsStarProjection e)
--       (her : e∈Set.range ((leftRestricted τ ω).comp (mapSequence f))) :
--       ∃ q : ℕ →ᵇ N, (∀ i, IsStarProjection (q i)) ∧ leftRestricted τ ω (mapSequence f q)=e
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.HilbertSequence.Pre` (definitions bundle `OAIQ039C011` of this split); `OAI.Kadison.TracialSequence.mapSequence` (definitions bundle `OAIQ039C018` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.HilbertSequence.instAddCommGroupPre` and `OAI.Kadison.HilbertSequence.instModuleComplexPre` (definitions bundle `OAIQ039C026` of this split); `OAI.Kadison.HilbertSequence.Space`, `OAI.Kadison.HilbertSequence.instInnerProductSpaceComplexPre` and `OAI.Kadison.HilbertSequence.instSeminormedAddCommGroupPre` (definitions bundle `OAIQ039C037` of this split); `OAI.Kadison.TracialSequence.boundedSubspace`, `OAI.Kadison.TracialSequence.instCompleteSpaceSubtypeSpaceGNSMemSubmoduleComplexBoundedSubspace` and `OAI.Kadison.TracialSequence.leftRestricted` (definitions bundle `OAIQ039C064` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialSequence.small_projection_lift` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C064

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder

open Filter UniformSpace Completion

namespace Kadison.TracialSequence

open TracialGNS HilbertSequence

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

variable [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

lemma projection_rep_lift {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (N : VonNeumannAlgebra G) (f : N →⋆ₐ[ℂ] A)
    {e : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω}
    (he : IsStarProjection e)
    (her : e∈Set.range ((leftRestricted τ ω).comp (mapSequence f))) :
    ∃ q : ℕ →ᵇ N, (∀ i, IsStarProjection (q i)) ∧ leftRestricted τ ω (mapSequence f q)=e := by
  sorry

end Kadison.TracialSequence

end

end OAI
end
