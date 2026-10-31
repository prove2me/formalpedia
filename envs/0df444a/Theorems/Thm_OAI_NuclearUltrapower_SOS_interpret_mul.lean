-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_interpret_mul
-- name    : OAI.NuclearUltrapower.SOS.interpret_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T08:48:48.331647+00:00
-- url     : https://prove2.me/theorems/c9ab23f8-09b3-401a-8b83-dd6e27625990
-- title:
--   OAI.NuclearUltrapower.SOS.interpret_mul: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.SOS.interpret_mul` of [lean/OAI/Analysis/NuclearUltrapower/SOSSemantics.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSSemantics.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS`):
--
--   ```lean
--   theorem interpret_mul (a b : Mat3) (ha : (toMatrix a).det = 1) (hb : (toMatrix b).det = 1) :
--       interpret (matMul a b) = interpret a * interpret b
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SOS.Mat3` (definitions bundle `OAIQ019N000` of this split); `OAI.NuclearUltrapower.SOS.SL` (definitions bundle `OAIQ019N001` of this split); `OAI.NuclearUltrapower.SOS.toMatrix` (definitions bundle `OAIQ019N039` of this split); `OAI.NuclearUltrapower.SOS.matMul` (definitions bundle `OAIQ019N047` of this split); `OAI.NuclearUltrapower.SOS.interpret` (definitions bundle `OAIQ019N048` of this split).
--
--   **Used by.** The proofs of `OAI.NuclearUltrapower.SOS.ElementarySpectral.value_mul`, `OAI.NuclearUltrapower.SOS.basis_good`, `OAI.NuclearUltrapower.SOS.gramPolyRow_good` and `OAI.NuclearUltrapower.SOS.residualRows_good` of this split import it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSSemantics.lean (declaration OAI.NuclearUltrapower.SOS.interpret_mul)

import Mathlib
import Definitions.Def_OAIQ019N048

section

attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS

theorem interpret_mul (a b : Mat3) (ha : (toMatrix a).det = 1) (hb : (toMatrix b).det = 1) :
    interpret (matMul a b) = interpret a * interpret b := by
  sorry

end NuclearUltrapower.SOS

end

end OAI
end
