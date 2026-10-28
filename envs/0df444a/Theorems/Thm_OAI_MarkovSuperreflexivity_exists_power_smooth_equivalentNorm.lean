-- Prove2me | Theorems.Thm_OAI_MarkovSuperreflexivity_exists_power_smooth_equivalentNorm
-- name    : OAI.MarkovSuperreflexivity.exists_power_smooth_equivalentNorm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T10:40:53.425725+00:00
-- url     : https://prove2.me/theorems/80383330-4de8-497c-ac05-897de689d8ee
-- title:
--   OAI.MarkovSuperreflexivity.exists_power_smooth_equivalentNorm: intermediate lemma from OpenAI, Nontrivial Markov Type Forces Superreflexivity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MarkovSuperreflexivity.hasNontrivialMarkovType_iff_hasEquivalentUCNorm`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nontrivial Markov Type Forces Superreflexivity*, OpenAI Math Release, September 23, 2026, result family 327, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MarkovSuperreflexivity.exists_power_smooth_equivalentNorm` of [lean/OAI/Analysis/MarkovType/MarkovType/PisierPowerRenorming.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/MarkovType/MarkovType/PisierPowerRenorming.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MarkovSuperreflexivity`):
--
--   ```lean
--   theorem exists_power_smooth_equivalentNorm [CompleteSpace X] (hUC : HasEquivalentUCNorm X) :
--       ∃ N : EquivalentNorm X, ∃ q : ℝ, 1 < q ∧ q ≤ 2 ∧
--         ∃ C : ℝ, 0 < C ∧ SymmetricPowerSmooth N.p q C ∧ PowerSmooth N.p q C ∧
--           (∀ t : ℝ, 0 ≤ t → smoothnessModulus N.p t ≤ C * t ^ q) ∧
--           UniformSmooth N.p
--   ```
--
--   **Definitions.** The statement is written with `OAI.MarkovSuperreflexivity.PowerSmooth`, `OAI.MarkovSuperreflexivity.SymmetricPowerSmooth` and `OAI.MarkovSuperreflexivity.UniformSmooth` (definitions bundle `OAISMk000` of this split); `OAI.MarkovSuperreflexivity.smoothnessModulus` (definitions bundle `OAISMk001` of this split); `OAI.MarkovSuperreflexivity.EquivalentNorm` and `OAI.MarkovSuperreflexivity.HasEquivalentUCNorm` (the published bundle `Def_MarkovType`).
--
--   **Used by.** The proof of `OAI.MarkovSuperreflexivity.hasNontrivialMarkovType_iff_hasEquivalentUCNorm` of this split imports it.
-- source:
--   OpenAI, Nontrivial Markov Type Forces Superreflexivity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 327; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nontrivial-Markov-Type-Forces-Superreflexivity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/MarkovType/MarkovType/PisierPowerRenorming.lean (declaration OAI.MarkovSuperreflexivity.exists_power_smooth_equivalentNorm)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MarkovType
import Definitions.Def_OAISMk000
import Definitions.Def_OAISMk001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkovSuperreflexivity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

omit [CompleteSpace X] in
theorem exists_power_smooth_equivalentNorm [CompleteSpace X] (hUC : HasEquivalentUCNorm X) :
    ∃ N : EquivalentNorm X, ∃ q : ℝ, 1 < q ∧ q ≤ 2 ∧
      ∃ C : ℝ, 0 < C ∧ SymmetricPowerSmooth N.p q C ∧ PowerSmooth N.p q C ∧
        (∀ t : ℝ, 0 ≤ t → smoothnessModulus N.p t ≤ C * t ^ q) ∧
        UniformSmooth N.p := by
  sorry

end MarkovSuperreflexivity

end OAI
end
