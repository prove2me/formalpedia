-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SL3Certificate_gram_row_120
-- name    : OAI.NuclearUltrapower.SL3Certificate.gram_row_120
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:34:13.714383+00:00
-- url     : https://prove2.me/theorems/2db8f867-6235-410b-a2d0-59baaf2915fd
-- title:
--   OAI.NuclearUltrapower.SL3Certificate.gram_row_120: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.SL3Certificate.gram_row_120` of [lean/OAI/Analysis/NuclearUltrapower/SOSCertificate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSCertificate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SL3Certificate`):
--
--   ```lean
--   theorem gram_row_120 : columns.map (dot q120) = g120
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SL3Certificate.q120` (definitions bundle `OAIQ019N004` of this split); `OAI.NuclearUltrapower.SL3Certificate.dot` (definitions bundle `OAIQ019N008` of this split); `OAI.NuclearUltrapower.SL3Certificate.g120` (definitions bundle `OAIQ019N019` of this split); `OAI.NuclearUltrapower.SL3Certificate.columns` (definitions bundle `OAIQ019N041` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.SOS.gramData_roots` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSCertificate.lean (declaration OAI.NuclearUltrapower.SL3Certificate.gram_row_120)

import Mathlib
import Definitions.Def_OAIQ019N041

section

attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SL3Certificate
theorem gram_row_120 : columns.map (dot q120) = g120 := by
  sorry
end NuclearUltrapower.SL3Certificate
end

end OAI
end
