-- Prove2me | Theorems.Thm_OAI_Kadison_OperatorAmplification_amplifiedStage_monotone
-- name    : OAI.Kadison.OperatorAmplification.amplifiedStage_monotone
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:50:33.118779+00:00
-- url     : https://prove2.me/theorems/75afde23-c04f-46ab-8a47-0d3b6d8ae1ea
-- title:
--   OAI.Kadison.OperatorAmplification.amplifiedStage_monotone: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.OperatorAmplification`, with `open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator`):
--
--   ```lean
--   lemma amplifiedStage_monotone (hE : Monotone (fun n => (E n).hom.range)) :
--       Monotone (fun n => (amplifiedStage ι i₀ M (E n)).hom.range)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.OperatorAmplification.SumSpace` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.OperatorAmplification.amplifiedTowerStageDecidableEq` (definitions bundle `OAIQ039C014` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.OperatorAmplification.matrixVonNeumann` (definitions bundle `OAIQ039C050` of this split); `OAI.Kadison.MatrixTower.Stage` (definitions bundle `OAIQ039C054` of this split); `OAI.Kadison.OperatorAmplification.amplifiedStage` (definitions bundle `OAIQ039C067` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.MatrixTower.exists_matrix_freeCornerPosition` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C067

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

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace Kadison.OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

variable (E : ℕ → MatrixTower.Stage M)

lemma amplifiedStage_monotone (hE : Monotone (fun n => (E n).hom.range)) :
    Monotone (fun n => (amplifiedStage ι i₀ M (E n)).hom.range) := by
  sorry

end Kadison.OperatorAmplification

end

end
end

end OAI
end
