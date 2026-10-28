-- Prove2me | Theorems.Thm_OAI_Kadison_MatrixCorners_normalizedStageAlphabet_orthonormal
-- name    : OAI.Kadison.MatrixCorners.normalizedStageAlphabet_orthonormal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:36:38.440738+00:00
-- url     : https://prove2.me/theorems/2a9e163e-7358-41d7-9864-9bd13ae218c4
-- title:
--   OAI.Kadison.MatrixCorners.normalizedStageAlphabet_orthonormal: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.MatrixCorners`, with `open scoped BigOperators ComplexOrder InnerProductSpace`):
--
--   ```lean
--   lemma normalizedStageAlphabet_orthonormal :
--       Orthonormal ℂ (fun g : G => TracialGNS.algebraVector τ (normalizedStageAlphabet φ p hp e α g))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.TracialGNS.algebraVector` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.MatrixCorners.normalizedStageAlphabet` and `OAI.Kadison.MatrixCorners.projectionIndices` (definitions bundle `OAIQ039C013` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialGNS.corner_arbitrarily_large_alphabet` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C003
import Definitions.Def_OAIQ039C013

section

attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace

namespace Kadison.MatrixCorners

attribute [local instance] Classical.propDecidable

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b, τ (a*b)=τ (b*a)) (h1 : τ 1=1)
  {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
  (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (p : Matrix I I ℂ) (hp : IsStarProjection p)
  {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  (e : G ≃ projectionIndices p hp)

variable (α : ℝ) (hα : 0<α) (hατ : τ (φ p)=(α:ℂ))

include hτ h1 hα hατ in
lemma normalizedStageAlphabet_orthonormal :
    Orthonormal ℂ (fun g : G => TracialGNS.algebraVector τ (normalizedStageAlphabet φ p hp e α g)) := by
  sorry

end Kadison.MatrixCorners

end

end
end

end OAI
end
