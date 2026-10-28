-- Prove2me | Theorems.Thm_OAI_Kadison_MatrixTower_generated_factor
-- name    : OAI.Kadison.MatrixTower.generated_factor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:59:42.170818+00:00
-- url     : https://prove2.me/theorems/ed3a0fd4-9217-4f1f-983b-7c418bf43e7e
-- title:
--   OAI.Kadison.MatrixTower.generated_factor: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.MatrixTower`, with `open scoped ComplexOrder BigOperators`):
--
--   ```lean
--   lemma generated_factor : FactorCorner.IsFactor (generated M F)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.FactorCorner.IsFactor` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.MatrixTower.Stage` (definitions bundle `OAIQ039C054` of this split); `OAI.Kadison.MatrixTower.generated` (definitions bundle `OAIQ039C071` of this split).
--
--   **Used by.** The proofs of `OAI.Kadison.MatrixTower.exists_matrix_freeCornerPosition` and `OAI.Kadison.MatrixTower.square_symmetry_after_average` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C071

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

open scoped ComplexOrder BigOperators

namespace Kadison.MatrixTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (F : ℕ → Stage M)

variable (hirr : ∀ a : M,(∀ n b,(F n).hom b*a=a*(F n).hom b) → ∃ z : ℂ,a=z • (1:M))

include hirr in
lemma generated_factor : FactorCorner.IsFactor (generated M F) := by
  sorry

end Kadison.MatrixTower

end

end
end

end OAI
end
