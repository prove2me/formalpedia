-- Prove2me | Theorems.Thm_OAI_Kadison_TracialSequence_constant_range_bicommutant_of_equiv
-- name    : OAI.Kadison.TracialSequence.constant_range_bicommutant_of_equiv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:44:36.446867+00:00
-- url     : https://prove2.me/theorems/8f568c79-bf3c-4d6b-a7c4-ba939ee5d963
-- title:
--   OAI.Kadison.TracialSequence.constant_range_bicommutant_of_equiv: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialSequence`, with `open scoped ComplexOrder Topology BoundedContinuousFunction`, `open TracialGNS`):
--
--   ```lean
--   lemma constant_range_bicommutant_of_equiv (hτ : ∀ a b : A,τ (a*b)=τ (b*a))
--       (htrace : ∀ a,σ (e a)=τ a) (hnormal : NormalGNS.BoundedWOTContinuous M σ) :
--       Set.centralizer (Set.centralizer (Set.range ((leftRestricted τ ω).comp constantSequence)))=Set.range ((leftRestricted τ ω).comp constantSequence)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.BoundedWOTContinuous` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.HilbertSequence.Pre` (definitions bundle `OAIQ039C011` of this split); `OAI.Kadison.TracialSequence.constantSequence` (definitions bundle `OAIQ039C018` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.HilbertSequence.instAddCommGroupPre` and `OAI.Kadison.HilbertSequence.instModuleComplexPre` (definitions bundle `OAIQ039C026` of this split); `OAI.Kadison.HilbertSequence.Space`, `OAI.Kadison.HilbertSequence.instInnerProductSpaceComplexPre` and `OAI.Kadison.HilbertSequence.instSeminormedAddCommGroupPre` (definitions bundle `OAIQ039C037` of this split); `OAI.Kadison.TracialSequence.boundedSubspace`, `OAI.Kadison.TracialSequence.instCompleteSpaceSubtypeSpaceGNSMemSubmoduleComplexBoundedSubspace` and `OAI.Kadison.TracialSequence.leftRestricted` (definitions bundle `OAIQ039C064` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialSequence.exists_freeCornerPosition_of_equiv_tower` of this split imports it.
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

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Topology BoundedContinuousFunction

namespace Kadison.TracialSequence

open TracialGNS

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (e : A ≃⋆ₐ[ℂ] M) (σ : M →ₚ[ℂ] ℂ)

lemma constant_range_bicommutant_of_equiv (hτ : ∀ a b : A,τ (a*b)=τ (b*a))
    (htrace : ∀ a,σ (e a)=τ a) (hnormal : NormalGNS.BoundedWOTContinuous M σ) :
    Set.centralizer (Set.centralizer (Set.range ((leftRestricted τ ω).comp constantSequence)))=Set.range ((leftRestricted τ ω).comp constantSequence) := by
  sorry

end Kadison.TracialSequence

end

end
end

end OAI
end
