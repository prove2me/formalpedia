-- Prove2me | Theorems.Thm_OAI_Kadison_NormalRepresentation_exists_orthogonal_links_of_faithful
-- name    : OAI.Kadison.NormalRepresentation.exists_orthogonal_links_of_faithful
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:42:22.528724+00:00
-- url     : https://prove2.me/theorems/16039f85-9319-473a-a17b-fe2a1ab38868
-- title:
--   OAI.Kadison.NormalRepresentation.exists_orthogonal_links_of_faithful: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.NormalRepresentation`, with `open scoped InnerProductSpace ComplexOrder Topology`, `open HilbertBiprod PartialIsometryOrder`):
--
--   ```lean
--   theorem exists_orthogonal_links_of_faithful
--       (hnormal : NormalGNS.BoundedWOTContinuous M τ)
--       (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) :
--       ∃ S : Set (Link (diagonalAlgebra M τ hnormal).commutant
--         (right (H:=H) (G:=τ.GNS)) left),
--         OrthogonalLinks _ _ _ S ∧ (familySpace _ _ _ S).starProjection=left
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.HilbertBiprod.Space` (definitions bundle `OAIQ039C000` of this split); `OAI.Kadison.PartialIsometryOrder.Link`, `OAI.Kadison.PartialIsometryOrder.OrthogonalLinks`, `OAI.Kadison.PartialIsometryOrder.familySpace` and `OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace` (definitions bundle `OAIQ039C001` of this split); `OAI.Kadison.NormalGNS.BoundedWOTContinuous` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.HilbertBiprod.left` and `OAI.Kadison.HilbertBiprod.right` (definitions bundle `OAIQ039C020` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.NormalRepresentation.diagonalAlgebra` (definitions bundle `OAIQ039C062` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.NormalRepresentation.exists_countable_gns_embedding` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C062

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

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.NormalRepresentation

open HilbertBiprod PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

theorem exists_orthogonal_links_of_faithful
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) :
    ∃ S : Set (Link (diagonalAlgebra M τ hnormal).commutant
      (right (H:=H) (G:=τ.GNS)) left),
      OrthogonalLinks _ _ _ S ∧ (familySpace _ _ _ S).starProjection=left := by
  sorry

end Kadison.NormalRepresentation

end

end
end

end OAI
end
