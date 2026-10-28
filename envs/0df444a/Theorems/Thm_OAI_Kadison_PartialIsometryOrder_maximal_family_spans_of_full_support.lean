-- Prove2me | Theorems.Thm_OAI_Kadison_PartialIsometryOrder_maximal_family_spans_of_full_support
-- name    : OAI.Kadison.PartialIsometryOrder.maximal_family_spans_of_full_support
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:37:11.27793+00:00
-- url     : https://prove2.me/theorems/9535f6c3-4412-4e4e-b153-76557654cd14
-- title:
--   OAI.Kadison.PartialIsometryOrder.maximal_family_spans_of_full_support: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.PartialIsometryOrder`, with `open scoped InnerProductSpace ComplexOrder Topology`):
--
--   ```lean
--   theorem maximal_family_spans_of_full_support
--       (hsupport : (FactorCorner.supportSpace M e).starProjection=1)
--       (heM : e∈M) (hfM : f∈M) (he : IsStarProjection e) (hf : IsStarProjection f)
--       (S : Set (Link M e f)) (hS : Maximal (OrthogonalLinks M e f) S) :
--       (familySpace M e f S).starProjection=f
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.PartialIsometryOrder.Link`, `OAI.Kadison.PartialIsometryOrder.OrthogonalLinks`, `OAI.Kadison.PartialIsometryOrder.familySpace` and `OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace` (definitions bundle `OAIQ039C001` of this split); `OAI.Kadison.FactorCorner.instCompleteSpaceSubtypeMemSubmoduleComplexSupportSpace` and `OAI.Kadison.FactorCorner.supportSpace` (definitions bundle `OAIQ039C008` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.NormalRepresentation.exists_orthogonal_links_of_faithful` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C001
import Definitions.Def_OAIQ039C008

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (e f : H →L[ℂ] H)

theorem maximal_family_spans_of_full_support
    (hsupport : (FactorCorner.supportSpace M e).starProjection=1)
    (heM : e∈M) (hfM : f∈M) (he : IsStarProjection e) (hf : IsStarProjection f)
    (S : Set (Link M e f)) (hS : Maximal (OrthogonalLinks M e f) S) :
    (familySpace M e f S).starProjection=f := by
  sorry

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end
