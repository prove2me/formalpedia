-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_Elementary_kazhdanSet_generates
-- name    : OAI.NuclearUltrapower.Elementary.kazhdanSet_generates
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T07:57:20.38849+00:00
-- url     : https://prove2.me/theorems/e5d46336-93d9-4226-9427-7ad52b7cbe26
-- title:
--   OAI.NuclearUltrapower.Elementary.kazhdanSet_generates: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.Elementary.kazhdanSet_generates` of [lean/OAI/Analysis/NuclearUltrapower/Kazhdan.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/Kazhdan.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.Elementary`, with `open scoped InnerProductSpace`, `open SOS SOSEnergy`, `open Displacement (dist)`):
--
--   ```lean
--   theorem kazhdanSet_generates : Subgroup.closure (kazhdanSet : Set IntegralGroup) = ⊤
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.IntegralVector3` (definitions bundle `OAIQ019N000` of this split); `OAI.NuclearUltrapower.SOS.SL` (definitions bundle `OAIQ019N001` of this split); `OAI.NuclearUltrapower.Elementary.kazhdanSet` (definitions bundle `OAIQ019N044` of this split); `OAI.NuclearUltrapower.Elementary.IntegralGroup`, `OAI.NuclearUltrapower.Elementary.integralAction` and `OAI.NuclearUltrapower.SOS.E` (definitions bundle `OAIQ019N049` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.main_statement` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/Kazhdan.lean (declaration OAI.NuclearUltrapower.Elementary.kazhdanSet_generates)

import Mathlib
import Definitions.Def_OAIQ019N044

section

attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower.Elementary
open SOS SOSEnergy
open Displacement (dist)

theorem kazhdanSet_generates : Subgroup.closure (kazhdanSet : Set IntegralGroup) = ⊤ := by
  sorry

end NuclearUltrapower.Elementary
end
end

end OAI
end
