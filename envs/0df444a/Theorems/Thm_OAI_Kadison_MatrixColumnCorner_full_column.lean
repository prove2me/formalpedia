-- Prove2me | Theorems.Thm_OAI_Kadison_MatrixColumnCorner_full_column
-- name    : OAI.Kadison.MatrixColumnCorner.full_column
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:29:52.330981+00:00
-- url     : https://prove2.me/theorems/2faf4f64-c39e-4f38-8268-407a0c0d3b73
-- title:
--   OAI.Kadison.MatrixColumnCorner.full_column: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.MatrixColumnCorner`, with `open scoped ComplexOrder Matrix.Norms.L2Operator`):
--
--   ```lean
--   lemma full_column (φ : Matrix I I ℂ →⋆ₐ[ℂ] D) (i0 : I) :
--       (∀ i j, star (φ (Matrix.single i i0 1))*φ (Matrix.single j i0 1)=
--         if i=j then φ (Matrix.single i0 i0 1) else 0) ∧
--       (∀ i, φ (Matrix.single i0 i0 1)*star (φ (Matrix.single i i0 1))=
--         star (φ (Matrix.single i i0 1))) ∧
--       ∑ i,φ (Matrix.single i i0 1)*star (φ (Matrix.single i i0 1))=1
--   ```
--
--   **Used by.** The proof of `OAI.Kadison.FreeBlocks.normal_free_corner_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Kadison.MatrixColumnCorner

variable {I D : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [CStarAlgebra D]

omit [Nonempty I] in
lemma full_column (φ : Matrix I I ℂ →⋆ₐ[ℂ] D) (i0 : I) :
    (∀ i j, star (φ (Matrix.single i i0 1))*φ (Matrix.single j i0 1)=
      if i=j then φ (Matrix.single i0 i0 1) else 0) ∧
    (∀ i, φ (Matrix.single i0 i0 1)*star (φ (Matrix.single i i0 1))=
      star (φ (Matrix.single i i0 1))) ∧
    ∑ i,φ (Matrix.single i i0 1)*star (φ (Matrix.single i i0 1))=1 := by
  sorry

end Kadison.MatrixColumnCorner

end

end
end

end OAI
end
