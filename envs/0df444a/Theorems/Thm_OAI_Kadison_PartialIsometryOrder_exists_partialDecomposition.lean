-- Prove2me | Theorems.Thm_OAI_Kadison_PartialIsometryOrder_exists_partialDecomposition
-- name    : OAI.Kadison.PartialIsometryOrder.exists_partialDecomposition
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:46:50.579806+00:00
-- url     : https://prove2.me/theorems/6f40fae1-3b83-4983-b29c-25c6a0ebd039
-- title:
--   OAI.Kadison.PartialIsometryOrder.exists_partialDecomposition: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.PartialIsometryOrder`, with `open scoped ComplexOrder InnerProductSpace Topology BigOperators`, `open Filter`):
--
--   ```lean
--   theorem exists_partialDecomposition (M : VonNeumannAlgebra H)
--       (hM : FactorCorner.IsFactor M) {p : H →L[ℂ] H}
--       (hpM : p∈M) (hp : IsStarProjection p) (hpn : p≠0) :
--       Nonempty (PartialDecomposition M p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.FactorCorner.IsFactor` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.PartialIsometryOrder.PartialDecomposition` (definitions bundle `OAIQ039C029` of this split).
--
--   **Used by.** The proofs of `OAI.Kadison.PartialIsometryOrder.DyadicPartition.exists_base_subEquivalent` and `OAI.Kadison.PartialIsometryOrder.nonfinite_two_isometries` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C029

section

attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

open Filter

universe u

namespace Kadison.PartialIsometryOrder

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_partialDecomposition (M : VonNeumannAlgebra H)
    (hM : FactorCorner.IsFactor M) {p : H →L[ℂ] H}
    (hpM : p∈M) (hp : IsStarProjection p) (hpn : p≠0) :
    Nonempty (PartialDecomposition M p) := by
  sorry

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end
