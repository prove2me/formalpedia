-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_nonuniqueness_without_compactness_inputs_q80
-- name    : OAI.BoltzmannNonuniqueness.nonuniqueness_without_compactness_inputs_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:32:44.265831+00:00
-- url     : https://prove2.me/theorems/d1c5277b-736d-4f41-80e2-5152ff3f513c
-- title:
--   OAI.BoltzmannNonuniqueness.nonuniqueness_without_compactness_inputs_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.nonuniqueness_without_compactness_inputs` of [lean/OAI/MathematicalPhysics/Boltzmann/Branching/PeriodicExistenceReduction.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Branching/PeriodicExistenceReduction.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness`):
--
--   ```lean
--   theorem nonuniqueness_without_compactness_inputs_q80
--       (hcarleman : Published.GPV2009CarlemanInput)
--       (hGLPS : Published.GLPS1988Proposition3)
--       (hperiodic : PeriodicExistenceInput) : NonuniquenessStatement
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.NonuniquenessStatement` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.PeriodicExistenceInput` (definitions bundle `OAIQ080A001` of this split); `OAI.BoltzmannNonuniqueness.Published.GLPS1988Proposition3` and `OAI.BoltzmannNonuniqueness.Published.GPV2009CarlemanInput` (definitions bundle `OAIQ080A002` of this split).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.nonuniqueness` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Branching/PeriodicExistenceReduction.lean (declaration OAI.BoltzmannNonuniqueness.nonuniqueness_without_compactness_inputs)

import Mathlib
import Definitions.Def_OAIQ080A002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BoltzmannNonuniqueness

theorem nonuniqueness_without_compactness_inputs_q80
    (hcarleman : Published.GPV2009CarlemanInput)
    (hGLPS : Published.GLPS1988Proposition3)
    (hperiodic : PeriodicExistenceInput) : NonuniquenessStatement := by
  sorry

end BoltzmannNonuniqueness

end

end OAI
end
