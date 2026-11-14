-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_bucket_aug_64_ca
-- name    : OAI.NuclearUltrapower.SOS.bucket_aug_64_ca
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T07:04:07.001188+00:00
-- url     : https://prove2.me/theorems/a92a6a30-5e62-4d98-9ed8-ace80f0eb6e0
-- title:
--   OAI.NuclearUltrapower.SOS.bucket_aug_64_ca: intermediate lemma from OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS`):
--
--   ```lean
--   theorem bucket_aug_64_ca : ((residualBucket 64).map Prod.snd).sum = -102848070
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SOS.Mat3` (definitions bundle `OAIQ229C003` of this split); `OAI.NuclearUltrapower.SOS.residualBucket` (definitions bundle `OAIQ229C027` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.SOS.residual_augmentation_ca` of this split imports it.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ229C027

section

attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
theorem bucket_aug_64_ca : ((residualBucket 64).map Prod.snd).sum = -102848070 := by
  sorry
end NuclearUltrapower.SOS
end

end OAI
end
