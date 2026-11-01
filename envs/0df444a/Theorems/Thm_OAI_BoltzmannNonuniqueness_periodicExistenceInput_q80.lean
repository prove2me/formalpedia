-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_periodicExistenceInput_q80
-- name    : OAI.BoltzmannNonuniqueness.periodicExistenceInput_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T18:16:23.815991+00:00
-- url     : https://prove2.me/theorems/73b2d48f-4be0-480c-96d1-dba9bc43cb2e
-- title:
--   OAI.BoltzmannNonuniqueness.periodicExistenceInput_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.periodicExistenceInput` of [lean/OAI/MathematicalPhysics/Boltzmann/Compactness/PeriodicExistenceDischarge.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/PeriodicExistenceDischarge.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness`, with `open MeasureTheory`, `open PeriodicApproximation`):
--
--   ```lean
--   theorem periodicExistenceInput_q80 : PeriodicExistenceInput
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.PeriodicExistenceInput` (definitions bundle `OAIQ080A001` of this split).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.nonuniqueness` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/PeriodicExistenceDischarge.lean (declaration OAI.BoltzmannNonuniqueness.periodicExistenceInput)

import Mathlib
import Definitions.Def_OAIQ080A001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness
open PeriodicApproximation

theorem periodicExistenceInput_q80 : PeriodicExistenceInput := by
  sorry

end BoltzmannNonuniqueness

end

end

end OAI
end
