-- Prove2me | Theorems.Thm_OAI_Kadison_uniform_commutator_nonfinite_factor
-- name    : OAI.Kadison.uniform_commutator_nonfinite_factor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:41:03.241683+00:00
-- url     : https://prove2.me/theorems/7ba2d81b-60d2-4be7-99e5-70c9fe4e1aa0
-- title:
--   OAI.Kadison.uniform_commutator_nonfinite_factor: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison`, with `open scoped ComplexOrder InnerProductSpace`):
--
--   ```lean
--   theorem uniform_commutator_nonfinite_factor (P : VonNeumannAlgebra H)
--       (hfac : FactorCorner.IsFactor P) (hfin : ¬PartialIsometryOrder.IsFiniteAlgebra P)
--       (Y : H →L[ℂ] H) (h : ℕ)
--       (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈P) :
--       ‖diagonalAmplification h Y*matrixOperator h X-
--         matrixOperator h X*diagonalAmplification h Y‖ ≤
--         9*commutatorSeminorm P Y*‖matrixOperator h X‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.FactorCorner.IsFactor` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.PartialIsometryOrder.IsFiniteAlgebra` (definitions bundle `OAIQ039C015` of this split); `OAI.Kadison.commutatorSeminorm`, `OAI.Kadison.diagonalAmplification` and `OAI.Kadison.matrixOperator` (the published bundle `Def_UniformCommutator`).
--
--   **Used by.** The proof of `OAI.Kadison.uniform_commutator_separable_factor` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C008
import Definitions.Def_OAIQ039C015

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem uniform_commutator_nonfinite_factor (P : VonNeumannAlgebra H)
    (hfac : FactorCorner.IsFactor P) (hfin : ¬PartialIsometryOrder.IsFiniteAlgebra P)
    (Y : H →L[ℂ] H) (h : ℕ)
    (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈P) :
    ‖diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y‖ ≤
      9*commutatorSeminorm P Y*‖matrixOperator h X‖ := by
  sorry

end Kadison

end

end
end

end OAI
end
