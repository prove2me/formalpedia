-- Prove2me | Theorems.Thm_OAI_Kadison_NormalRepresentation_exists_countable_gns_embedding
-- name    : OAI.Kadison.NormalRepresentation.exists_countable_gns_embedding
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:46:02.874555+00:00
-- url     : https://prove2.me/theorems/d8d6254b-0a5c-4fee-8f5d-d5c9cb6bd506
-- title:
--   OAI.Kadison.NormalRepresentation.exists_countable_gns_embedding: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.NormalRepresentation`, with `open scoped Topology InnerProductSpace ComplexOrder`):
--
--   ```lean
--   theorem exists_countable_gns_embedding [TopologicalSpace.SeparableSpace H]
--       (hnormal : NormalGNS.BoundedWOTContinuous M τ)
--       (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) :
--       ∃ ι : Type u, Countable ι ∧ ∃ V : H →ₗᵢ[ℂ] lp (fun _ : ι => τ.GNS) 2,
--         ∀ (a : M) (x : H) (i : ι),V (a.val x) i=τ.gnsStarAlgHom a (V x i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.BoundedWOTContinuous` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.NormalRepresentation.exists_stable_gns_model` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C022

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped Topology InnerProductSpace ComplexOrder

universe u

namespace Kadison.NormalRepresentation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

theorem exists_countable_gns_embedding [TopologicalSpace.SeparableSpace H]
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) :
    ∃ ι : Type u, Countable ι ∧ ∃ V : H →ₗᵢ[ℂ] lp (fun _ : ι => τ.GNS) 2,
      ∀ (a : M) (x : H) (i : ι),V (a.val x) i=τ.gnsStarAlgHom a (V x i) := by
  sorry

end Kadison.NormalRepresentation

end

end
end

end OAI
end
