-- Prove2me | Theorems.Thm_OAI_Kadison_MatrixGNS_flattenCopies_commutator_norm
-- name    : OAI.Kadison.MatrixGNS.flattenCopies_commutator_norm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:45:40.933499+00:00
-- url     : https://prove2.me/theorems/389d6d44-0edd-456e-88d4-ee5d1160b844
-- title:
--   OAI.Kadison.MatrixGNS.flattenCopies_commutator_norm: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.MatrixGNS`, with `open scoped BigOperators InnerProductSpace`, `open ContinuousLinearMap`, `open OperatorAmplification CyclicColumns`):
--
--   ```lean
--   lemma flattenCopies_commutator_norm (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
--       (Y : H →L[ℂ] H) (X : CStarMatrix κ κ (CStarMatrix ι ι A)) :
--       ‖diagonal (H:=SumSpace (H:=H) ι) κ (diagonal (H:=H) ι Y)*
--           matrixRepresentation (ι:=κ) (H:=SumSpace (H:=H) ι) (matrixRepresentation (ι:=ι) ρ) X-
--         matrixRepresentation (ι:=κ) (H:=SumSpace (H:=H) ι) (matrixRepresentation (ι:=ι) ρ) X*
--           diagonal (H:=SumSpace (H:=H) ι) κ (diagonal (H:=H) ι Y)‖=
--       ‖diagonal (H:=H) (κ×ι) Y*matrixRepresentation ρ (flatten ι κ X)-
--           matrixRepresentation ρ (flatten ι κ X)*diagonal (H:=H) (κ×ι) Y‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.OperatorAmplification.SumSpace` and `OAI.Kadison.OperatorAmplification.diagonal` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.CyclicColumns.instDecidableEq_solutions` (definitions bundle `OAIQ039C004` of this split); `OAI.Kadison.MatrixGNS.flatten` and `OAI.Kadison.MatrixGNS.matrixFlattenRepresentationCopiesDecidableEq` (definitions bundle `OAIQ039C013` of this split); `OAI.Kadison.CyclicColumns.matrixRepresentation` (definitions bundle `OAIQ039C022` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.MatrixGNS.flatBalanced_commutator_dominates` of this split imports it.
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

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap

namespace Kadison.MatrixGNS

open OperatorAmplification CyclicColumns

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

attribute [local instance] OAI.Kadison.MatrixGNS.matrixFlattenRepresentationCopiesDecidableEq
lemma flattenCopies_commutator_norm (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Y : H →L[ℂ] H) (X : CStarMatrix κ κ (CStarMatrix ι ι A)) :
    ‖diagonal (H:=SumSpace (H:=H) ι) κ (diagonal (H:=H) ι Y)*
        matrixRepresentation (ι:=κ) (H:=SumSpace (H:=H) ι) (matrixRepresentation (ι:=ι) ρ) X-
      matrixRepresentation (ι:=κ) (H:=SumSpace (H:=H) ι) (matrixRepresentation (ι:=ι) ρ) X*
        diagonal (H:=SumSpace (H:=H) ι) κ (diagonal (H:=H) ι Y)‖=
    ‖diagonal (H:=H) (κ×ι) Y*matrixRepresentation ρ (flatten ι κ X)-
        matrixRepresentation ρ (flatten ι κ X)*diagonal (H:=H) (κ×ι) Y‖ := by
  sorry

end Kadison.MatrixGNS

end

end
end

end OAI
end
