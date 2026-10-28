-- Prove2me | Theorems.Thm_OAI_Kadison_BiprodLinkColumn_component_intertwines
-- name    : OAI.Kadison.BiprodLinkColumn.component_intertwines
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:40:47.861176+00:00
-- url     : https://prove2.me/theorems/52e4862a-b3c4-44b4-8a00-ec30bed452b5
-- title:
--   OAI.Kadison.BiprodLinkColumn.component_intertwines: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.BiprodLinkColumn`, with `open scoped ComplexOrder InnerProductSpace Topology`, `open Filter`, `open HilbertBiprod PartialIsometryOrder HilbertFiniteMaps`):
--
--   ```lean
--   lemma component_intertwines {A : Type*} [CStarAlgebra A]
--       (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G))
--       (v : Intertwiner N) (a : A)
--       (hv : block (φ a) (ψ a)*star v.val=star v.val*block (φ a) (ψ a)) :
--       (component N v).comp (φ a)=(ψ a).comp (component N v)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.HilbertBiprod.Space` and `OAI.Kadison.HilbertBiprod.block` (definitions bundle `OAIQ039C000` of this split); `OAI.Kadison.PartialIsometryOrder.Link` (definitions bundle `OAIQ039C001` of this split); `OAI.Kadison.BiprodLinkColumn.Intertwiner`, `OAI.Kadison.BiprodLinkColumn.component`, `OAI.Kadison.HilbertBiprod.left` and `OAI.Kadison.HilbertBiprod.right` (definitions bundle `OAIQ039C020` of this split).
--
--   **Used by.** The proofs of `OAI.Kadison.HilbertModuleSB.exists_unitary_of_embeddings` and `OAI.Kadison.NormalRepresentation.link_intertwines` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C020

section

attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

open Filter

namespace Kadison.BiprodLinkColumn

open HilbertBiprod PartialIsometryOrder HilbertFiniteMaps

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable (N : VonNeumannAlgebra (Space H G))

variable (S : Set (Intertwiner N)) (hS : OrthogonalLinks N right left S)

include hS

omit hS

lemma component_intertwines {A : Type*} [CStarAlgebra A]
    (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G))
    (v : Intertwiner N) (a : A)
    (hv : block (φ a) (ψ a)*star v.val=star v.val*block (φ a) (ψ a)) :
    (component N v).comp (φ a)=(ψ a).comp (component N v) := by
  sorry

end Kadison.BiprodLinkColumn

end

end
end

end OAI
end
