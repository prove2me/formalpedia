-- Prove2me | Theorems.Thm_OAI_Kadison_TracialSequence_trace_mul
-- name    : OAI.Kadison.TracialSequence.trace_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:58:14.858191+00:00
-- url     : https://prove2.me/theorems/d1b3e093-376f-4022-b7da-28d5482253cf
-- title:
--   OAI.Kadison.TracialSequence.trace_mul: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialSequence`, with `open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder`, `open Filter UniformSpace Completion`, `open TracialGNS HilbertSequence`):
--
--   ```lean
--   lemma trace_mul (a b : ℕ →ᵇ A) : sequenceTrace τ ω (leftRestricted τ ω (a*b))=
--       sequenceTrace τ ω (leftRestricted τ ω (b*a))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.HilbertSequence.Pre` (definitions bundle `OAIQ039C011` of this split); `OAI.Kadison.HilbertSequence.instAddCommGroupPre` and `OAI.Kadison.HilbertSequence.instModuleComplexPre` (definitions bundle `OAIQ039C026` of this split); `OAI.Kadison.HilbertSequence.Space`, `OAI.Kadison.HilbertSequence.instInnerProductSpaceComplexPre` and `OAI.Kadison.HilbertSequence.instSeminormedAddCommGroupPre` (definitions bundle `OAIQ039C037` of this split); `OAI.Kadison.TracialSequence.boundedSubspace`, `OAI.Kadison.TracialSequence.instCompleteSpaceSubtypeSpaceGNSMemSubmoduleComplexBoundedSubspace` and `OAI.Kadison.TracialSequence.leftRestricted` (definitions bundle `OAIQ039C064` of this split); `OAI.Kadison.TracialSequence.sequenceTrace` (definitions bundle `OAIQ039C069` of this split).
--
--   **Used by.** The proofs of `OAI.Kadison.TracialSequence.bicommutant_trace_mul` and `OAI.Kadison.TracialSequence.sequenceUnitary_free` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C069

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

namespace Kadison

namespace TracialSequence

open TracialGNS HilbertSequence

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

include hτ in
lemma trace_mul (a b : ℕ →ᵇ A) : sequenceTrace τ ω (leftRestricted τ ω (a*b))=
    sequenceTrace τ ω (leftRestricted τ ω (b*a)) := by
  sorry

end TracialSequence

end Kadison

end

end
end

end OAI
end
