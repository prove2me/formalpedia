-- Prove2me | Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixInclusion_entry
-- name    : OAI.Kadison.OperatorAmplification.matrixInclusion_entry
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:43:33.758137+00:00
-- url     : https://prove2.me/theorems/2fd0c115-6d12-4c1c-a5d8-42c4e7a50cd8
-- title:
--   OAI.Kadison.OperatorAmplification.matrixInclusion_entry: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.OperatorAmplification`, with `open scoped BigOperators InnerProductSpace ComplexOrder`):
--
--   ```lean
--   lemma matrixInclusion_entry (X : matrixVonNeumann ι i₀ Q) (i j : ι) :
--       (matrixInclusion ι i₀ M Q hQM X i j:H →L[ℂ] H)=
--         entry ι (X:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) i j
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.OperatorAmplification.SumSpace` and `OAI.Kadison.OperatorAmplification.entry` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.OperatorAmplification.matrixCornerInclusionDecidableEq` (definitions bundle `OAIQ039C015` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.OperatorAmplification.matrixVonNeumann` (definitions bundle `OAIQ039C050` of this split); `OAI.Kadison.OperatorAmplification.matrixInclusion` (definitions bundle `OAIQ039C063` of this split).
--
--   **Used by.** The proofs of `OAI.Kadison.OperatorAmplification.matrixInclusion_commutes`, `OAI.Kadison.OperatorAmplification.matrixInclusion_row` and `OAI.Kadison.OperatorAmplification.matrixTrace_restrict` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C063

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M Q : VonNeumannAlgebra H) (hQM : Q≤M)

attribute [local instance] OAI.Kadison.OperatorAmplification.matrixCornerInclusionDecidableEq
lemma matrixInclusion_entry (X : matrixVonNeumann ι i₀ Q) (i j : ι) :
    (matrixInclusion ι i₀ M Q hQM X i j:H →L[ℂ] H)=
      entry ι (X:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) i j := by
  sorry

end Kadison.OperatorAmplification

end

end
end

end OAI
end
