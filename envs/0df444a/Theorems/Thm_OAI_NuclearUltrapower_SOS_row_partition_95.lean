-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_row_partition_95
-- name    : OAI.NuclearUltrapower.SOS.row_partition_95
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T10:49:37.793351+00:00
-- url     : https://prove2.me/theorems/3266d007-b57e-463b-8f4b-bc796e2bebca
-- title:
--   OAI.NuclearUltrapower.SOS.row_partition_95: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.SOS.row_partition_95` of [lean/OAI/Analysis/NuclearUltrapower/SOSResidual.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSResidual.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS`):
--
--   ```lean
--   theorem row_partition_95 : normalize matLe residualRow95 = normalize matLe rowBuckets95.flatten
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SOS.Mat3` and `OAI.NuclearUltrapower.SOS.Poly` (definitions bundle `OAIQ019N000` of this split); `OAI.NuclearUltrapower.SOS.residualRow95` (definitions bundle `OAIQ019N043` of this split); `OAI.NuclearUltrapower.SOS.matLe` and `OAI.NuclearUltrapower.SOS.normalize` (definitions bundle `OAIQ019N047` of this split); `OAI.NuclearUltrapower.SOS.rowBuckets95` (definitions bundle `OAIQ019N049` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.SOS.row_normalizations` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSResidual.lean (declaration OAI.NuclearUltrapower.SOS.row_partition_95)

import Mathlib
import Definitions.Def_OAIQ019N049
import Definitions.Def_OAIQ019N043

section

attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
theorem row_partition_95 : normalize matLe residualRow95 = normalize matLe rowBuckets95.flatten := by
  sorry
end NuclearUltrapower.SOS
end

end OAI
end
