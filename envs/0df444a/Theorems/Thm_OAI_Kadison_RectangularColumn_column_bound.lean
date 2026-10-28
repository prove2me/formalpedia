-- Prove2me | Theorems.Thm_OAI_Kadison_RectangularColumn_column_bound
-- name    : OAI.Kadison.RectangularColumn.column_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:37:51.247518+00:00
-- url     : https://prove2.me/theorems/6b89fc17-3043-4e83-a06c-6e4e1ba79bbe
-- title:
--   OAI.Kadison.RectangularColumn.column_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.RectangularColumn`, with `open scoped InnerProductSpace BigOperators`):
--
--   ```lean
--   theorem column_bound [PartialOrder A] [StarOrderedRing A] {ι : Type*} [Fintype ι]
--       (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F))
--       (Δ : A →L[ℂ] (K →L[ℂ] F))
--       (hΔ : ∀ a b, Δ (a*b)=(Δ a).comp (σ b)+(lam a).comp (Δ b))
--       (a : ι → A) (ξ : K) :
--       ‖WithLp.toLp 2 (fun i => Δ (a i) ξ)‖≤
--         (4*‖Δ‖)*CyclicColumns.columnNorm a*‖ξ‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.CyclicColumns.columnNorm` (definitions bundle `OAIQ039C004` of this split); `OAI.Kadison.RectangularColumn.instNormedSpaceComplexContinuousLinearMapId_solutions` (definitions bundle `OAIQ039C016` of this split).
--
--   **Used by.** The proofs of `OAI.Kadison.CyclicSpatial.exists_embedded_cyclic_intertwiner` and `OAI.Kadison.commutator_column_bound` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C004
import Definitions.Def_OAIQ039C016

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

open scoped InnerProductSpace BigOperators

namespace Kadison.RectangularColumn

variable {A K F : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

attribute [local instance] OAI.Kadison.RectangularColumn.instNormedAddCommGroupContinuousLinearMapComplexId_solutions
attribute [local instance] OAI.Kadison.RectangularColumn.instNormedSpaceComplexContinuousLinearMapId_solutions
theorem column_bound [PartialOrder A] [StarOrderedRing A] {ι : Type*} [Fintype ι]
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (Δ : A →L[ℂ] (K →L[ℂ] F))
    (hΔ : ∀ a b, Δ (a*b)=(Δ a).comp (σ b)+(lam a).comp (Δ b))
    (a : ι → A) (ξ : K) :
    ‖WithLp.toLp 2 (fun i => Δ (a i) ξ)‖≤
      (4*‖Δ‖)*CyclicColumns.columnNorm a*‖ξ‖ := by
  sorry

end Kadison.RectangularColumn

end

end
end

end OAI
end
