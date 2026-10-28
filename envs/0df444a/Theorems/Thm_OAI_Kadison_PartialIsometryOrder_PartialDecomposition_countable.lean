-- Prove2me | Theorems.Thm_OAI_Kadison_PartialIsometryOrder_PartialDecomposition_countable
-- name    : OAI.Kadison.PartialIsometryOrder.PartialDecomposition.countable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:47:35.078187+00:00
-- url     : https://prove2.me/theorems/476b1abf-c9c3-4e95-925d-0477acde190a
-- title:
--   OAI.Kadison.PartialIsometryOrder.PartialDecomposition.countable: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.PartialIsometryOrder.PartialDecomposition`, with `open scoped InnerProductSpace`):
--
--   ```lean
--   theorem countable : Countable D.I
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.PartialIsometryOrder.PartialDecomposition` (definitions bundle `OAIQ039C029` of this split).
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

open scoped InnerProductSpace

namespace Kadison.PartialIsometryOrder.PartialDecomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

variable {M : VonNeumannAlgebra H} {p : H →L[ℂ] H} (D : PartialDecomposition M p)

theorem countable : Countable D.I := by
  sorry

end Kadison.PartialIsometryOrder.PartialDecomposition

end

end
end

end OAI
end
