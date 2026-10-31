-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_eval_scale
-- name    : OAI.NuclearUltrapower.SOS.eval_scale
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T08:42:19.164992+00:00
-- url     : https://prove2.me/theorems/5c38a521-d209-44d2-bd6c-6aea1812823e
-- title:
--   OAI.NuclearUltrapower.SOS.eval_scale: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.SOS.eval_scale` of [lean/OAI/Analysis/NuclearUltrapower/SOSSemantics.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSSemantics.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS`):
--
--   ```lean
--   theorem eval_scale (f : α → A) (ps : Poly α) (k : ℤ) :
--       eval f (ps.map (fun p => (p.1, k*p.2))) = k • eval f ps
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SOS.Poly` and `OAI.NuclearUltrapower.SOS.eval` (definitions bundle `OAIQ019N000` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.SOS.residual_value_generic` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSSemantics.lean (declaration OAI.NuclearUltrapower.SOS.eval_scale)

import Mathlib
import Definitions.Def_OAIQ019N000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
variable {α A : Type*} [DecidableEq α]

section EvalOperations
variable [Ring A]
omit [DecidableEq α] in
theorem eval_scale (f : α → A) (ps : Poly α) (k : ℤ) :
    eval f (ps.map (fun p => (p.1, k*p.2))) = k • eval f ps := by
  sorry

end EvalOperations
end NuclearUltrapower.SOS

end

end OAI
end
