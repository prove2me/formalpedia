-- Prove2me | Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixTrace_diagonal
-- name    : OAI.Kadison.OperatorAmplification.matrixTrace_diagonal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:52:12.758566+00:00
-- url     : https://prove2.me/theorems/4063ffa8-5a96-4212-8300-f3bc9932d022
-- title:
--   OAI.Kadison.OperatorAmplification.matrixTrace_diagonal: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.OperatorAmplification`, with `open scoped BigOperators InnerProductSpace ComplexOrder`):
--
--   ```lean
--   lemma matrixTrace_diagonal (τ : M →ₚ[ℂ] ℂ) (a : M) :
--       matrixTrace ι i₀ M τ (diagonalHom ι i₀ M a)=τ a
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.OperatorAmplification.SumSpace` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.OperatorAmplification.instDecidableEq_solutions_1` and `OAI.Kadison.OperatorAmplification.matrixDiffuseTransferIndexDecidableEq` (definitions bundle `OAIQ039C014` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.OperatorAmplification.matrixVonNeumann` (definitions bundle `OAIQ039C050` of this split); `OAI.Kadison.OperatorAmplification.diagonalHom` (definitions bundle `OAIQ039C062` of this split); `OAI.Kadison.OperatorAmplification.matrixTrace` (definitions bundle `OAIQ039C068` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.OperatorAmplification.matrix_diffuse_of_stages` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C062
import Definitions.Def_OAIQ039C068

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

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

attribute [local instance] OAI.Kadison.OperatorAmplification.matrixDiffuseTransferIndexDecidableEq
lemma matrixTrace_diagonal (τ : M →ₚ[ℂ] ℂ) (a : M) :
    matrixTrace ι i₀ M τ (diagonalHom ι i₀ M a)=τ a := by
  sorry

end Kadison.OperatorAmplification

end

end
end

end OAI
end
