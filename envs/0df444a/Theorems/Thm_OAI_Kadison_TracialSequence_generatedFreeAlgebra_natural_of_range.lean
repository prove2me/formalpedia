-- Prove2me | Theorems.Thm_OAI_Kadison_TracialSequence_generatedFreeAlgebra_natural_of_range
-- name    : OAI.Kadison.TracialSequence.generatedFreeAlgebra_natural_of_range
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:03:18.816664+00:00
-- url     : https://prove2.me/theorems/d045b56b-f3ef-4001-93f5-2cb40426e90d
-- title:
--   OAI.Kadison.TracialSequence.generatedFreeAlgebra_natural_of_range: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialSequence`, with `open scoped ComplexOrder InnerProductSpace`):
--
--   ```lean
--   lemma generatedFreeAlgebra_natural_of_range
--       {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
--       (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
--       (D : VonNeumannAlgebra (boundedSubspace τ ω))
--       {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
--       (Q : VonNeumannAlgebra K) (j : Q →⋆ₐ[ℂ] A)
--       (hD : ∀ d : D,(d:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
--         Set.range ((leftRestricted τ ω).comp (mapSequence j)))
--       (a : generatedFreeAlgebra τ ω D) :
--       (a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
--         Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.HilbertSequence.Pre` (definitions bundle `OAIQ039C011` of this split); `OAI.Kadison.TracialSequence.mapSequence` (definitions bundle `OAIQ039C018` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.HilbertSequence.instAddCommGroupPre` and `OAI.Kadison.HilbertSequence.instModuleComplexPre` (definitions bundle `OAIQ039C026` of this split); `OAI.Kadison.HilbertSequence.Space`, `OAI.Kadison.HilbertSequence.instInnerProductSpaceComplexPre` and `OAI.Kadison.HilbertSequence.instSeminormedAddCommGroupPre` (definitions bundle `OAIQ039C037` of this split); `OAI.Kadison.TracialSequence.boundedSubspace`, `OAI.Kadison.TracialSequence.instCompleteSpaceSubtypeSpaceGNSMemSubmoduleComplexBoundedSubspace` and `OAI.Kadison.TracialSequence.leftRestricted` (definitions bundle `OAIQ039C064` of this split); `OAI.Kadison.TracialSequence.generatedFreeAlgebra` (definitions bundle `OAIQ039C072` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialSequence.generated_free_small_corners_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C072

section

attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace

namespace Kadison.TracialSequence

lemma generatedFreeAlgebra_natural_of_range
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (D : VonNeumannAlgebra (boundedSubspace τ ω))
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (Q : VonNeumannAlgebra K) (j : Q →⋆ₐ[ℂ] A)
    (hD : ∀ d : D,(d:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
      Set.range ((leftRestricted τ ω).comp (mapSequence j)))
    (a : generatedFreeAlgebra τ ω D) :
    (a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
      Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))) := by
  sorry

end Kadison.TracialSequence

end

end
end

end OAI
end
