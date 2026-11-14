-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_residual_augmentation_ca
-- name    : OAI.NuclearUltrapower.SOS.residual_augmentation_ca
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T09:42:16.617053+00:00
-- url     : https://prove2.me/theorems/c1efab32-ee0a-4b54-8712-28dcfdc9306b
-- title:
--   OAI.NuclearUltrapower.SOS.residual_augmentation_ca: intermediate lemma from OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS`):
--
--   ```lean
--   theorem residual_augmentation_ca : augmentation residual = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SOS.Mat3` (definitions bundle `OAIQ229C003` of this split); `OAI.NuclearUltrapower.SOS.augmentation` (definitions bundle `OAIQ229C023` of this split); `OAI.NuclearUltrapower.SOS.residual` (definitions bundle `OAIQ229C031` of this split).
--
--   **Used by.** The proofs of `OAI_CoarseAssembly_provedKazhdanInput_ca`, `OAI.CoarseAssembly.publishedKazhdanInput_of_elementaryReduction_ca` and `OAI_NuclearUltrapower_SOS_ElementarySpectral_deltaOp_gap_ca` of this split import it.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ229C031

section

attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
variable {A : Type*} [AddCommGroup A]

theorem residual_augmentation_ca : augmentation residual = 0 := by
  sorry
end NuclearUltrapower.SOS
end

end OAI
end
