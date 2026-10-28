-- Prove2me | Theorems.Thm_OAI_Kadison_MatrixDiffuse_noMinimal_of_matrix_stages
-- name    : OAI.Kadison.MatrixDiffuse.noMinimal_of_matrix_stages
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:44:51.741808+00:00
-- url     : https://prove2.me/theorems/e8b65fde-6cea-4c96-978c-1ca48a297a8c
-- title:
--   OAI.Kadison.MatrixDiffuse.noMinimal_of_matrix_stages: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.MatrixDiffuse`, with `open scoped ComplexOrder InnerProductSpace`, `open Matrix`):
--
--   ```lean
--   theorem noMinimal_of_matrix_stages (hM : FactorCorner.IsFactor M)
--       (hfaith : ∀ a∈M, τ (star a*a)=0 → a=0)
--       (n : ℕ → ℕ) (φ : ∀ j, Matrix (Fin (n j)) (Fin (n j)) ℂ →⋆ₐ[ℂ] M)
--       (hsize : ∀ N : ℕ, ∃ j, N<n j) : DiffuseProjection.HasNoMinimalProjections M
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.DiffuseProjection.HasNoMinimalProjections` and `OAI.Kadison.FactorCorner.IsFactor` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialSequence.freeCornerPosition_of_unitary_abstract` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C008
import Definitions.Def_OAIQ039C022

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.MatrixDiffuse

open Matrix

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : (H →L[ℂ] H) →ₚ[ℂ] ℂ)

variable (hτ : ∀ a∈M, ∀ b∈M, τ (a*b)=τ (b*a)) (h1 : τ 1=1)

include hτ h1

theorem noMinimal_of_matrix_stages (hM : FactorCorner.IsFactor M)
    (hfaith : ∀ a∈M, τ (star a*a)=0 → a=0)
    (n : ℕ → ℕ) (φ : ∀ j, Matrix (Fin (n j)) (Fin (n j)) ℂ →⋆ₐ[ℂ] M)
    (hsize : ∀ N : ℕ, ∃ j, N<n j) : DiffuseProjection.HasNoMinimalProjections M := by
  sorry

end Kadison.MatrixDiffuse

end

end
end

end OAI
end
