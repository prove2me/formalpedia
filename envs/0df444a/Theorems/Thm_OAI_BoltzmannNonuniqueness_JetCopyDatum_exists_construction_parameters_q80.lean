-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_exists_construction_parameters_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_construction_parameters_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:26:14.72999+00:00
-- url     : https://prove2.me/theorems/95ab4f06-0f02-43cd-805c-c6f798af2759
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_construction_parameters_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_construction_parameters` of [lean/OAI/MathematicalPhysics/Boltzmann/Branching/MainParameters.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Branching/MainParameters.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum`, with `open scoped ENNReal`):
--
--   ```lean
--   theorem exists_construction_parameters_q80
--       (hDP : Published.DunfordPettis1940HotPairWindows)
--       (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
--       (hMityagin : Published.Mityagin2020FiveGainParameters) : Nonempty ConstructionParameters
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.JetCopyDatum.ConstructionParameters` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.Published.DunfordPettis1940HotPairWindows`, `OAI.BoltzmannNonuniqueness.Published.GLPS1988Proposition3`, `OAI.BoltzmannNonuniqueness.Published.GPV2009CarlemanInput` and `OAI.BoltzmannNonuniqueness.Published.Mityagin2020FiveGainParameters` (definitions bundle `OAIQ080A002` of this split).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.nonuniqueness_without_compactness_inputs_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Branching/MainParameters.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_construction_parameters)

import Mathlib
import Definitions.Def_OAIQ080A002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal
namespace BoltzmannNonuniqueness.JetCopyDatum

theorem exists_construction_parameters_q80
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hMityagin : Published.Mityagin2020FiveGainParameters) : Nonempty ConstructionParameters := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum

end

end OAI
end
