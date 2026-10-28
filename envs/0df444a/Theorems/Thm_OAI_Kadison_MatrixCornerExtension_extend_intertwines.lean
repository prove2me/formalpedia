-- Prove2me | Theorems.Thm_OAI_Kadison_MatrixCornerExtension_extend_intertwines
-- name    : OAI.Kadison.MatrixCornerExtension.extend_intertwines
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:56:10.385819+00:00
-- url     : https://prove2.me/theorems/e4b00d55-9f44-4a50-9ac1-459b578946e9
-- title:
--   OAI.Kadison.MatrixCornerExtension.extend_intertwines: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.MatrixCornerExtension`, with `open scoped InnerProductSpace`, `open ContinuousLinearMap`, `open MatrixCornerHilbert`):
--
--   ```lean
--   lemma extend_intertwines (T : fixedSpace (σ p) →L[ℂ] fixedSpace (ρ p))
--       (hT : ∀ a : Corner hp, T.comp (ReducingRepresentation.corner σ hp a)=
--         (ReducingRepresentation.corner ρ hp a).comp T) (a : A) :
--       (extend σ ρ v hcol hinit htotal T).comp (σ a)=
--         (ρ a).comp (extend σ ρ v hcol hinit htotal T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.Corner`, `OAI.Kadison.instAlgebraComplexCorner`, `OAI.Kadison.instRingCorner`, `OAI.Kadison.instStarRingCorner`, `OAI.Kadison.MatrixCornerHilbert.fixedSpace`, `OAI.Kadison.MatrixCornerHilbert.instCompleteSpaceSubtypeMemSubmoduleComplexFixedSpace` and `OAI.Kadison.ReducingRepresentation.corner` (definitions bundle `OAIQ039C004` of this split); `OAI.Kadison.MatrixCornerExtension.extend` (definitions bundle `OAIQ039C038` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.MatrixCornerImplementation.exists_matrix_corner_intertwiner` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C038

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

namespace Kadison.MatrixCornerExtension

open MatrixCornerHilbert

variable {A K H ι : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [DecidableEq ι]

variable (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

variable {p : A} (hp : IsStarProjection p) (v : ι → A)
  (hcol : ∀ i j, star (v i)*v j=if i=j then p else 0)
  (hinit : ∀ i, p*star (v i)=star (v i))
  (htotal : ∑ i, v i*star (v i)=1)

lemma extend_intertwines (T : fixedSpace (σ p) →L[ℂ] fixedSpace (ρ p))
    (hT : ∀ a : Corner hp, T.comp (ReducingRepresentation.corner σ hp a)=
      (ReducingRepresentation.corner ρ hp a).comp T) (a : A) :
    (extend σ ρ v hcol hinit htotal T).comp (σ a)=
      (ρ a).comp (extend σ ρ v hcol hinit htotal T) := by
  sorry

end Kadison.MatrixCornerExtension

end

end
end

end OAI
end
