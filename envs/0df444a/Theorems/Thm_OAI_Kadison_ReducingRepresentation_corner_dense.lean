-- Prove2me | Theorems.Thm_OAI_Kadison_ReducingRepresentation_corner_dense
-- name    : OAI.Kadison.ReducingRepresentation.corner_dense
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:37:49.463229+00:00
-- url     : https://prove2.me/theorems/b890b958-016d-44cc-8312-a51b25c6a3fe
-- title:
--   OAI.Kadison.ReducingRepresentation.corner_dense: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.ReducingRepresentation`, with `open scoped InnerProductSpace`, `open ContinuousLinearMap`, `open MatrixCornerHilbert`):
--
--   ```lean
--   lemma corner_dense (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {p : A} (hp : IsStarProjection p)
--       (Ω : H) (hΩ : DenseRange (fun a : A => σ a Ω)) (hpΩ : σ p Ω=Ω) :
--       DenseRange (fun a : Corner hp => corner σ hp a
--         (⟨Ω,(mem_fixedSpace _ _).mpr hpΩ⟩ : fixedSpace (σ p)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.Corner`, `OAI.Kadison.instAlgebraComplexCorner`, `OAI.Kadison.instRingCorner`, `OAI.Kadison.instStarRingCorner`, `OAI.Kadison.MatrixCornerHilbert.fixedSpace`, `OAI.Kadison.MatrixCornerHilbert.instCompleteSpaceSubtypeMemSubmoduleComplexFixedSpace`, `OAI.Kadison.MatrixCornerHilbert.mem_fixedSpace` and `OAI.Kadison.ReducingRepresentation.corner` (definitions bundle `OAIQ039C004` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.MatrixCornerImplementation.exists_matrix_corner_intertwiner` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.ReducingRepresentation

open MatrixCornerHilbert

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma corner_dense (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {p : A} (hp : IsStarProjection p)
    (Ω : H) (hΩ : DenseRange (fun a : A => σ a Ω)) (hpΩ : σ p Ω=Ω) :
    DenseRange (fun a : Corner hp => corner σ hp a
      (⟨Ω,(mem_fixedSpace _ _).mpr hpΩ⟩ : fixedSpace (σ p))) := by
  sorry

end Kadison.ReducingRepresentation

end

end
end

end OAI
end
