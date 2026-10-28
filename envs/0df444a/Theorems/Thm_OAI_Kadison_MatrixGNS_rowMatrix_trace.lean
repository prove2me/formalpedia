-- Prove2me | Theorems.Thm_OAI_Kadison_MatrixGNS_rowMatrix_trace
-- name    : OAI.Kadison.MatrixGNS.rowMatrix_trace
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:40:03.722962+00:00
-- url     : https://prove2.me/theorems/62f65ba3-a598-404e-bf53-4489abd68012
-- title:
--   OAI.Kadison.MatrixGNS.rowMatrix_trace: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.MatrixGNS`, with `open scoped BigOperators InnerProductSpace ComplexOrder`):
--
--   ```lean
--   lemma rowMatrix_trace (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1=1) (i : ι) :
--       trace (ι:=ι) τ (rowMatrix i (1:A))=(Fintype.card ι : ℂ)⁻¹
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.MatrixGNS.rowMatrix` (definitions bundle `OAIQ039C013` of this split); `OAI.Kadison.MatrixGNS.trace` (definitions bundle `OAIQ039C061` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.OperatorAmplification.matrix_small_corner_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C061

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.MatrixGNS

variable {A ι : Type*} [CStarAlgebra A] [Fintype ι]

attribute [local instance] OAI.Kadison.MatrixGNS.matrixRowCornerDecidableEq
variable [PartialOrder A] [StarOrderedRing A]

lemma rowMatrix_trace (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1=1) (i : ι) :
    trace (ι:=ι) τ (rowMatrix i (1:A))=(Fintype.card ι : ℂ)⁻¹ := by
  sorry

end Kadison.MatrixGNS

end

end
end

end OAI
end
