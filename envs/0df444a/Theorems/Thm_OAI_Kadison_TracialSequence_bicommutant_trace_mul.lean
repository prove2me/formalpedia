-- Prove2me | Theorems.Thm_OAI_Kadison_TracialSequence_bicommutant_trace_mul
-- name    : OAI.Kadison.TracialSequence.bicommutant_trace_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:54:45.369593+00:00
-- url     : https://prove2.me/theorems/7de0e8d5-9e82-43a1-8fd6-02ce9b30320f
-- title:
--   OAI.Kadison.TracialSequence.bicommutant_trace_mul: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialSequence`, with `open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder`, `open Filter UniformSpace Completion`, `open TracialGNS HilbertSequence`):
--
--   ```lean
--   theorem bicommutant_trace_mul
--       {S T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω}
--       (hS : S∈Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
--       (hT : T∈Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω)))) :
--       sequenceTrace τ ω (S*T)=sequenceTrace τ ω (T*S)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.HilbertSequence.Pre` (definitions bundle `OAIQ039C011` of this split); `OAI.Kadison.HilbertSequence.instAddCommGroupPre` and `OAI.Kadison.HilbertSequence.instModuleComplexPre` (definitions bundle `OAIQ039C026` of this split); `OAI.Kadison.HilbertSequence.Space`, `OAI.Kadison.HilbertSequence.instInnerProductSpaceComplexPre` and `OAI.Kadison.HilbertSequence.instSeminormedAddCommGroupPre` (definitions bundle `OAIQ039C037` of this split); `OAI.Kadison.TracialSequence.boundedSubspace`, `OAI.Kadison.TracialSequence.instCompleteSpaceSubtypeSpaceGNSMemSubmoduleComplexBoundedSubspace` and `OAI.Kadison.TracialSequence.leftRestricted` (definitions bundle `OAIQ039C064` of this split); `OAI.Kadison.TracialSequence.sequenceTrace` (definitions bundle `OAIQ039C069` of this split).
--
--   **Used by.** The proofs of `OAI.Kadison.TracialSequence.freeCornerPosition_of_unitary_abstract` and `OAI.Kadison.TracialSequence.subalgebra_tracial` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C069

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

open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder

open Filter UniformSpace Completion

namespace Kadison.TracialSequence

open TracialGNS HilbertSequence

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (hτ : ∀ a b : A, τ (a*b)=τ (b*a)) (hω : (ω : Filter ℕ)≤atTop)

include hτ hω in
theorem bicommutant_trace_mul
    {S T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω}
    (hS : S∈Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
    (hT : T∈Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω)))) :
    sequenceTrace τ ω (S*T)=sequenceTrace τ ω (T*S) := by
  sorry

end Kadison.TracialSequence

end

end
end

end OAI
end
