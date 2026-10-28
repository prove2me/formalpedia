-- Prove2me | Theorems.Thm_OAI_Kadison_FinitePatching_PartialUnitary_chain_upper_with_L2_and_membership
-- name    : OAI.Kadison.FinitePatching.PartialUnitary.chain_upper_with_L2_and_membership
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:57:18.116019+00:00
-- url     : https://prove2.me/theorems/a96b6b86-c428-41d8-b962-96d495b99f85
-- title:
--   OAI.Kadison.FinitePatching.PartialUnitary.chain_upper_with_L2_and_membership: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FinitePatching.PartialUnitary`, with `open scoped ComplexOrder InnerProductSpace Topology`, `open Filter ContinuousLinearMapWOT`):
--
--   ```lean
--   theorem chain_upper_with_L2_and_membership (τ : M →ₚ[ℂ] ℂ)
--       (hnormal : NormalGNS.BoundedWOTContinuous M τ)
--       (c : Set (PartialUnitary M)) (hc : IsChain (·≤·) c) (hne : c.Nonempty) :
--       ∃ v : PartialUnitary M, (∀ w∈c,w ≤ v) ∧
--         (∀ R : VonNeumannAlgebra H, (∀ w∈c,(w.val : H →L[ℂ] H)∈R) →
--           (v.val : H →L[ℂ] H)∈R) ∧
--         ∃ ω : Ultrafilter c, (ω : Filter c) ≤ atTop ∧
--           Tendsto (fun w : c => (τ w.val.support).re) (ω : Filter c) (𝓝 (τ v.support).re) ∧
--           Tendsto (fun w : c => TracialL2.norm τ (v.val-w.val.val)) (ω : Filter c) (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.BoundedWOTContinuous` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.FinitePatching.PartialUnitary` (definitions bundle `OAIQ039C009` of this split); `OAI.Kadison.TracialL2.norm` (definitions bundle `OAIQ039C017` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.FinitePatching.PartialUnitary.instPartialOrder` (definitions bundle `OAIQ039C046` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FinitePatching.admissible_chain_upper` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C017
import Definitions.Def_OAIQ039C046

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

open Filter ContinuousLinearMapWOT

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

namespace Kadison.FinitePatching

namespace PartialUnitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

theorem chain_upper_with_L2_and_membership (τ : M →ₚ[ℂ] ℂ)
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (c : Set (PartialUnitary M)) (hc : IsChain (·≤·) c) (hne : c.Nonempty) :
    ∃ v : PartialUnitary M, (∀ w∈c,w ≤ v) ∧
      (∀ R : VonNeumannAlgebra H, (∀ w∈c,(w.val : H →L[ℂ] H)∈R) →
        (v.val : H →L[ℂ] H)∈R) ∧
      ∃ ω : Ultrafilter c, (ω : Filter c) ≤ atTop ∧
        Tendsto (fun w : c => (τ w.val.support).re) (ω : Filter c) (𝓝 (τ v.support).re) ∧
        Tendsto (fun w : c => TracialL2.norm τ (v.val-w.val.val)) (ω : Filter c) (𝓝 0) := by
  sorry

end PartialUnitary

end Kadison.FinitePatching

end

end
end

end OAI
end
