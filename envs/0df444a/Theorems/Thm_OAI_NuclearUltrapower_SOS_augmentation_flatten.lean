-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_augmentation_flatten
-- name    : OAI.NuclearUltrapower.SOS.augmentation_flatten
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T08:42:47.500267+00:00
-- url     : https://prove2.me/theorems/1670977c-c28c-4fcb-9a12-1efb7a92576a
-- title:
--   OAI.NuclearUltrapower.SOS.augmentation_flatten: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.SOS.augmentation_flatten` of [lean/OAI/Analysis/NuclearUltrapower/SOSSemantics.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSSemantics.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS`):
--
--   ```lean
--   theorem augmentation_flatten {α : Type*} (rs : List (Poly α)) :
--       augmentation rs.flatten = (rs.map augmentation).sum
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SOS.Poly` (definitions bundle `OAIQ019N000` of this split); `OAI.NuclearUltrapower.SOS.augmentation` (definitions bundle `OAIQ019N047` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.SOS.residual_augmentation` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSSemantics.lean (declaration OAI.NuclearUltrapower.SOS.augmentation_flatten)

import Mathlib
import Definitions.Def_OAIQ019N047

section

attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
variable {A : Type*} [AddCommGroup A]

theorem augmentation_flatten {α : Type*} (rs : List (Poly α)) :
    augmentation rs.flatten = (rs.map augmentation).sum := by
  sorry

end NuclearUltrapower.SOS
end

end OAI
end
