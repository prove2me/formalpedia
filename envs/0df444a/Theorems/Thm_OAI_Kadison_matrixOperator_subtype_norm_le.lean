-- Prove2me | Theorems.Thm_OAI_Kadison_matrixOperator_subtype_norm_le
-- name    : OAI.Kadison.matrixOperator_subtype_norm_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:49:50.159154+00:00
-- url     : https://prove2.me/theorems/08406a2b-00af-4483-9d36-69316ed04b5a
-- title:
--   OAI.Kadison.matrixOperator_subtype_norm_le: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison`, with `open scoped ComplexOrder InnerProductSpace`):
--
--   ```lean
--   lemma matrixOperator_subtype_norm_le (M : VonNeumannAlgebra H)
--       (ψ : M →⋆ₐ[ℂ] (G →L[ℂ] G)) (h : ℕ)
--       (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈M) :
--       ‖matrixOperator h (fun i j => ψ ⟨X i j,hX i j⟩)‖≤‖matrixOperator h X‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.matrixOperator` (the published bundle `Def_UniformCommutator`).
--
--   **Used by.** The proofs of `OAI.Kadison.CentralSpectral.separable_uniform_bound` and `OAI.Kadison.NormalRepresentation.finite_standard_compression_bound` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_UniformCommutator
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

open scoped ComplexOrder InnerProductSpace

namespace Kadison

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma matrixOperator_subtype_norm_le (M : VonNeumannAlgebra H)
    (ψ : M →⋆ₐ[ℂ] (G →L[ℂ] G)) (h : ℕ)
    (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈M) :
    ‖matrixOperator h (fun i j => ψ ⟨X i j,hX i j⟩)‖≤‖matrixOperator h X‖ := by
  sorry

end Kadison

end

end
end

end OAI
end
