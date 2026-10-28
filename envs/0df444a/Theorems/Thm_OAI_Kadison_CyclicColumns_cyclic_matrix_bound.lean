-- Prove2me | Theorems.Thm_OAI_Kadison_CyclicColumns_cyclic_matrix_bound
-- name    : OAI.Kadison.CyclicColumns.cyclic_matrix_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:33:30.402653+00:00
-- url     : https://prove2.me/theorems/add4af46-e7a6-44fa-a829-6e29bd8d58c5
-- title:
--   OAI.Kadison.CyclicColumns.cyclic_matrix_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.CyclicColumns`, with `open scoped BigOperators ComplexOrder InnerProductSpace`):
--
--   ```lean
--   theorem cyclic_matrix_bound (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
--       (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (Δ : A →L[ℂ] (H →L[ℂ] F))
--       (hΔ : ∀ a b, Δ (a*b)=(Δ a).comp (σ b)+(lam a).comp (Δ b))
--       (Ω : H) (hΩ : DenseRange (fun a : A => σ a Ω)) (c : ℝ) (hc : 0 ≤ c)
--       (hcol : ∀ (v : ι → A) (ζ : H),
--         ‖WithLp.toLp 2 (fun i => Δ (v i) ζ)‖ ≤ c*columnNorm v*‖ζ‖)
--       (X : CStarMatrix ι ι A) :
--       ‖matrixAction (fun i j => Δ (X i j))‖ ≤ 4*c*‖X‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.CyclicColumns.columnNorm` and `OAI.Kadison.CyclicColumns.matrixAction` (definitions bundle `OAIQ039C004` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.CyclicSpatial.exists_cyclic_intertwiner` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C004

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

open scoped BigOperators ComplexOrder InnerProductSpace

namespace Kadison.CyclicColumns

variable {A H F ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [Fintype ι]

theorem cyclic_matrix_bound (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (Δ : A →L[ℂ] (H →L[ℂ] F))
    (hΔ : ∀ a b, Δ (a*b)=(Δ a).comp (σ b)+(lam a).comp (Δ b))
    (Ω : H) (hΩ : DenseRange (fun a : A => σ a Ω)) (c : ℝ) (hc : 0 ≤ c)
    (hcol : ∀ (v : ι → A) (ζ : H),
      ‖WithLp.toLp 2 (fun i => Δ (v i) ζ)‖ ≤ c*columnNorm v*‖ζ‖)
    (X : CStarMatrix ι ι A) :
    ‖matrixAction (fun i j => Δ (X i j))‖ ≤ 4*c*‖X‖ := by
  sorry

end Kadison.CyclicColumns

end

end
end

end OAI
end
