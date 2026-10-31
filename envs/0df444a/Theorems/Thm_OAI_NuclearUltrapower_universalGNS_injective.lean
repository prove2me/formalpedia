-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_universalGNS_injective
-- name    : OAI.NuclearUltrapower.universalGNS_injective
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:59:51.288061+00:00
-- url     : https://prove2.me/theorems/90165499-3b5b-45a6-8ccc-05a70436d8b4
-- title:
--   OAI.NuclearUltrapower.universalGNS_injective: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.universalGNS_injective` of [lean/OAI/Analysis/NuclearUltrapower/FaithfulGNS.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/FaithfulGNS.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower`, with `open scoped ComplexOrder ENNReal`):
--
--   ```lean
--   theorem universalGNS_injective : Function.Injective (universalGNS (A := A))
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.gnsSpectralOrder` and `OAI.NuclearUltrapower.gnsSpectralOrderedRing` (definitions bundle `OAIQ019N020` of this split); `OAI.NuclearUltrapower.UniversalGNS` and `OAI.NuclearUltrapower.universalGNS` (definitions bundle `OAIQ019N041` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.fullGroup_no_nuclear_ultrapower` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/FaithfulGNS.lean (declaration OAI.NuclearUltrapower.universalGNS_injective)

import Mathlib
import Definitions.Def_OAIQ019N041

section

attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instCompleteSpaceAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
universe u
open scoped ComplexOrder ENNReal
namespace NuclearUltrapower
variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

attribute [local instance] OAI.NuclearUltrapower.gnsSpectralOrder
attribute [local instance] OAI.NuclearUltrapower.gnsSpectralOrderedRing
theorem universalGNS_injective : Function.Injective (universalGNS (A := A)) := by
  sorry

end NuclearUltrapower
end
end

end OAI
end
