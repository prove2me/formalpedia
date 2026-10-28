-- Prove2me | Theorems.Thm_OAI_Kadison_MatrixGNS_row_corner_commutator_bound
-- name    : OAI.Kadison.MatrixGNS.row_corner_commutator_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:45:38.844054+00:00
-- url     : https://prove2.me/theorems/c8482f03-8dcc-46e7-b640-f4290506f07e
-- title:
--   OAI.Kadison.MatrixGNS.row_corner_commutator_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.MatrixGNS`, with `open scoped BigOperators InnerProductSpace ComplexOrder`):
--
--   ```lean
--   lemma row_corner_commutator_bound (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
--       (T : H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c)
--       (hT : ∀ a : A,‖T*σ a-σ a*T‖ ≤ c*‖a‖) (i : ι)
--       (X : CStarMatrix ι ι A) (hX : rowMatrix i (1:A)*X*rowMatrix i (1:A)=X) :
--       ‖OperatorAmplification.diagonal (H:=H) ι T*CyclicColumns.matrixRepresentation σ X-
--         CyclicColumns.matrixRepresentation σ X*OperatorAmplification.diagonal (H:=H) ι T‖ ≤ c*‖X‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.OperatorAmplification.SumSpace` and `OAI.Kadison.OperatorAmplification.diagonal` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.CyclicColumns.instDecidableEq_solutions` (definitions bundle `OAIQ039C004` of this split); `OAI.Kadison.MatrixGNS.rowMatrix` (definitions bundle `OAIQ039C013` of this split); `OAI.Kadison.CyclicColumns.matrixRepresentation` (definitions bundle `OAIQ039C022` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.OperatorAmplification.matrix_small_corner_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C013
import Definitions.Def_OAIQ039C022

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma row_corner_commutator_bound (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (T : H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c)
    (hT : ∀ a : A,‖T*σ a-σ a*T‖ ≤ c*‖a‖) (i : ι)
    (X : CStarMatrix ι ι A) (hX : rowMatrix i (1:A)*X*rowMatrix i (1:A)=X) :
    ‖OperatorAmplification.diagonal (H:=H) ι T*CyclicColumns.matrixRepresentation σ X-
      CyclicColumns.matrixRepresentation σ X*OperatorAmplification.diagonal (H:=H) ι T‖ ≤ c*‖X‖ := by
  sorry

end Kadison.MatrixGNS

end

end
end

end OAI
end
