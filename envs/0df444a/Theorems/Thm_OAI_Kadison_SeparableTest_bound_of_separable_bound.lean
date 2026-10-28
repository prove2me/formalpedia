-- Prove2me | Theorems.Thm_OAI_Kadison_SeparableTest_bound_of_separable_bound
-- name    : OAI.Kadison.SeparableTest.bound_of_separable_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:21:28.990792+00:00
-- url     : https://prove2.me/theorems/53c9a8b3-952b-44b3-b500-b73a28757f49
-- title:
--   OAI.Kadison.SeparableTest.bound_of_separable_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.SeparableTest`, with `open scoped InnerProductSpace BigOperators`):
--
--   ```lean
--   theorem bound_of_separable_bound {c : ℝ} (hc : 0 ≤ c)
--       (hsep : SeparableBound.{u} c) (hh : 1≤h) :
--       ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖≤
--         c*commutatorSeminorm P Y*‖matrixOperator h X‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.SeparableTest.SeparableBound` (definitions bundle `OAIQ039C030` of this split); `OAI.Kadison.commutatorSeminorm`, `OAI.Kadison.diagonalAmplification` and `OAI.Kadison.matrixOperator` (the published bundle `Def_UniformCommutator`).
--
--   **Used by.** The proof of `OAI.Kadison.uniform_commutator` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C030

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

open scoped InnerProductSpace BigOperators

universe u

namespace Kadison.SeparableTest

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H) (h : ℕ)
  (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈P)

include hX

theorem bound_of_separable_bound {c : ℝ} (hc : 0 ≤ c)
    (hsep : SeparableBound.{u} c) (hh : 1≤h) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖≤
      c*commutatorSeminorm P Y*‖matrixOperator h X‖ := by
  sorry

end Kadison.SeparableTest

end

end
end

end OAI
end
