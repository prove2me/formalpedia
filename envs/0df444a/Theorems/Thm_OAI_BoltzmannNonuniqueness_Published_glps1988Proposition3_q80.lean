-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_Published_glps1988Proposition3_q80
-- name    : OAI.BoltzmannNonuniqueness.Published.glps1988Proposition3_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:32:08.894895+00:00
-- url     : https://prove2.me/theorems/2f2eb4d2-5528-4c01-aa9e-f668f4c04736
-- title:
--   OAI.BoltzmannNonuniqueness.Published.glps1988Proposition3_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.Published.glps1988Proposition3` of [lean/OAI/MathematicalPhysics/Boltzmann/Branching/VelocityAveraging.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Branching/VelocityAveraging.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.Published`, with `open MeasureTheory Filter Set`, `open scoped Topology ENNReal`):
--
--   ```lean
--   theorem glps1988Proposition3_q80 : GLPS1988Proposition3
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.Published.GLPS1988Proposition3` (definitions bundle `OAIQ080A002` of this split).
--
--   **Used by.** The proofs of `OAI.BoltzmannNonuniqueness.PeriodicApproximation.approximatingSolution_renormalized_average_compactness_q80` and `OAI.BoltzmannNonuniqueness.nonuniqueness` of this split import it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Branching/VelocityAveraging.lean (declaration OAI.BoltzmannNonuniqueness.Published.glps1988Proposition3)

import Mathlib
import Definitions.Def_OAIQ080A002

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.Published

theorem glps1988Proposition3_q80 : GLPS1988Proposition3 := by
  sorry

end BoltzmannNonuniqueness.Published

end

end OAI
end
