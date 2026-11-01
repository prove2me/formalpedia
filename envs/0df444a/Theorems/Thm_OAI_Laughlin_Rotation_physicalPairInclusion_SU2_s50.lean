-- Prove2me | Theorems.Thm_OAI_Laughlin_Rotation_physicalPairInclusion_SU2_s50
-- name    : OAI.Laughlin.Rotation.physicalPairInclusion_SU2_s50
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T20:56:11.264875+00:00
-- url     : https://prove2.me/theorems/2470b900-dd7a-4318-a544-63370e4843d4
-- title:
--   OAI.Laughlin.Rotation.physicalPairInclusion_SU2_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Rotation.physicalPairInclusion_SU2` of [lean/OAI/Analysis/Laughlin/Operators/PhysicalPairRotation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Operators/PhysicalPairRotation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Rotation`, with `open scoped BigOperators Matrix Kronecker`):
--
--   ```lean
--   theorem physicalPairInclusion_SU2_s50 (Q : ℕ) (hQ : 0 < Q) (g : SourceSU2) :
--       (sourceSpinRepresentation Q g ⊗ₖ sourceSpinRepresentation Q g)*physicalPairInclusion Q =
--         physicalPairInclusion Q*sourceSpinRepresentation (2*Q-2) g
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Rotation.SourceSU2` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Rotation.physicalPairInclusion` (definitions bundle `OAIQ050L013` of this split); `OAI.Laughlin.Rotation.sourceSpinRepresentation` (definitions bundle `OAIQ050L016` of this split).
--
--   **Used by.** The proofs of `OAI.Laughlin.Fock.sourceFourVector_rotation_s50` and `OAI.Laughlin.Fock.sourcePairEnd_rotation_s50` of this split import it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Operators/PhysicalPairRotation.lean (declaration OAI.Laughlin.Rotation.physicalPairInclusion_SU2)

import Mathlib
import Definitions.Def_OAIQ050L013
import Definitions.Def_OAIQ050L016

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix Kronecker

theorem physicalPairInclusion_SU2_s50 (Q : ℕ) (hQ : 0 < Q) (g : SourceSU2) :
    (sourceSpinRepresentation Q g ⊗ₖ sourceSpinRepresentation Q g)*physicalPairInclusion Q =
      physicalPairInclusion Q*sourceSpinRepresentation (2*Q-2) g := by
  sorry

end Laughlin.Rotation

end OAI
end
