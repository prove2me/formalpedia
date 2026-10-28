-- Prove2me | Theorems.Thm_OAI_MarkovSuperreflexivity_MarkovTypeWith_not_coordinatesRepresentable
-- name    : OAI.MarkovSuperreflexivity.MarkovTypeWith.not_coordinatesRepresentable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T10:40:34.907699+00:00
-- url     : https://prove2.me/theorems/a2790f28-4473-4238-a63f-721b5678be19
-- title:
--   OAI.MarkovSuperreflexivity.MarkovTypeWith.not_coordinatesRepresentable: intermediate lemma from OpenAI, Nontrivial Markov Type Forces Superreflexivity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MarkovSuperreflexivity.hasNontrivialMarkovType_iff_hasEquivalentUCNorm`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nontrivial Markov Type Forces Superreflexivity*, OpenAI Math Release, September 23, 2026, result family 327, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MarkovSuperreflexivity.MarkovTypeWith.not_coordinatesRepresentable` of [lean/OAI/Analysis/MarkovType/MarkovType/MarkovObstruction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/MarkovType/MarkovType/MarkovObstruction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MarkovSuperreflexivity`):
--
--   ```lean
--   theorem MarkovTypeWith.not_coordinatesRepresentable {p K : ℝ}
--       (hX : MarkovTypeWith p K X) (hp : 1 < p) (N : OrderedNorm) :
--       ¬ CoordinatesRepresentable X N
--   ```
--
--   **Definitions.** The statement is written with `OAI.MarkovSuperreflexivity.CoordinatesRepresentable` and `OAI.MarkovSuperreflexivity.OrderedNorm` (definitions bundle `OAISMk000` of this split); `OAI.MarkovSuperreflexivity.MarkovTypeWith` (the published bundle `Def_MarkovType`).
--
--   **Used by.** The proof of `OAI.MarkovSuperreflexivity.hasNontrivialMarkovType_iff_hasEquivalentUCNorm` of this split imports it.
-- source:
--   OpenAI, Nontrivial Markov Type Forces Superreflexivity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 327; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nontrivial-Markov-Type-Forces-Superreflexivity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/MarkovType/MarkovType/MarkovObstruction.lean (declaration OAI.MarkovSuperreflexivity.MarkovTypeWith.not_coordinatesRepresentable)

import Mathlib
import Init.Data.List.Count
import Lean.Elab.Tactic.Omega
import Definitions.Def_MarkovType
import Definitions.Def_OAISMk000

section

attribute [-instance] _root_.OAI.MarkovSuperreflexivity.sequenceL2ExponentAtLeastOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem MarkovTypeWith.not_coordinatesRepresentable {p K : ℝ}
    (hX : MarkovTypeWith p K X) (hp : 1 < p) (N : OrderedNorm) :
    ¬ CoordinatesRepresentable X N := by
  sorry

end MarkovSuperreflexivity

end

end OAI
end
