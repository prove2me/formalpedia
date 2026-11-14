-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_bucket_l1_74_ca
-- name    : OAI.NuclearUltrapower.SOS.bucket_l1_74_ca
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T09:53:40.581238+00:00
-- url     : https://prove2.me/theorems/779f1030-ed4f-4d97-b867-f367f37e7a60
-- title:
--   OAI.NuclearUltrapower.SOS.bucket_l1_74_ca: intermediate lemma from OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS`):
--
--   ```lean
--   theorem bucket_l1_74_ca : intL1 (residualBucket 74) = 139470840
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SOS.Mat3` (definitions bundle `OAIQ229C003` of this split); `OAI.NuclearUltrapower.SOS.intL1` (definitions bundle `OAIQ229C015` of this split); `OAI.NuclearUltrapower.SOS.residualBucket` (definitions bundle `OAIQ229C027` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.SOS.residual_l1_ca` of this split imports it.
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
theorem bucket_l1_74_ca : intL1 (residualBucket 74) = 139470840 := by
  sorry
end NuclearUltrapower.SOS
end

end OAI
end
