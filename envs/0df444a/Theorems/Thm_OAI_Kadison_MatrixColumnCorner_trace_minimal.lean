-- Prove2me | Theorems.Thm_OAI_Kadison_MatrixColumnCorner_trace_minimal
-- name    : OAI.Kadison.MatrixColumnCorner.trace_minimal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:30:17.805477+00:00
-- url     : https://prove2.me/theorems/eb0eb494-cf0d-4c82-abe5-d354a886dd59
-- title:
--   OAI.Kadison.MatrixColumnCorner.trace_minimal: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.MatrixColumnCorner`, with `open scoped ComplexOrder Matrix.Norms.L2Operator`):
--
--   ```lean
--   lemma trace_minimal [PartialOrder D] [StarOrderedRing D]
--       (τ : D →ₚ[ℂ] ℂ) (hτ : ∀ a b, τ (a*b)=τ (b*a)) (h1 : τ 1=1)
--       (φ : Matrix I I ℂ →⋆ₐ[ℂ] D) (i : I) :
--       τ (φ (Matrix.single i i 1))=(Fintype.card I : ℂ)⁻¹
--   ```
--
--   **Used by.** The proofs of `OAI.Kadison.FreeBlocks.normal_free_corner_bound` and `OAI.Kadison.MatrixTower.small_of_stages` of this split import it.
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

lemma trace_minimal [PartialOrder D] [StarOrderedRing D]
    (τ : D →ₚ[ℂ] ℂ) (hτ : ∀ a b, τ (a*b)=τ (b*a)) (h1 : τ 1=1)
    (φ : Matrix I I ℂ →⋆ₐ[ℂ] D) (i : I) :
    τ (φ (Matrix.single i i 1))=(Fintype.card I : ℂ)⁻¹ := by
  sorry

end Kadison.MatrixColumnCorner

end

end
end

end OAI
end
