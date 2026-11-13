-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_row_partition_113_ca
-- name    : OAI.NuclearUltrapower.SOS.row_partition_113_ca
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:36:19.000756+00:00
-- url     : https://prove2.me/theorems/cacfe03b-80a5-4a4f-96a9-036540ba4aa3
-- title:
--   OAI.NuclearUltrapower.SOS.row_partition_113_ca: intermediate lemma from OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS`):
--
--   ```lean
--   theorem row_partition_113_ca : normalize matLe residualRow113 = normalize matLe rowBuckets113.flatten
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SOS.Mat3` and `OAI.NuclearUltrapower.SOS.Poly` (definitions bundle `OAIQ229C003` of this split); `OAI.NuclearUltrapower.SOS.matLe`, `OAI.NuclearUltrapower.SOS.normalize` and `OAI.NuclearUltrapower.SOS.residualRow113` (definitions bundle `OAIQ229C015` of this split); `OAI.NuclearUltrapower.SOS.rowBuckets113` (definitions bundle `OAIQ229C020` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.SOS.row_normalizations_ca` of this split imports it.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ229C015
import Definitions.Def_OAIQ229C020

section

attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
theorem row_partition_113_ca : normalize matLe residualRow113 = normalize matLe rowBuckets113.flatten := by
  sorry
end NuclearUltrapower.SOS
end

end OAI
end
