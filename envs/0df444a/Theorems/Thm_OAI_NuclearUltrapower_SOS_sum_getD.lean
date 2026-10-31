-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_sum_getD
-- name    : OAI.NuclearUltrapower.SOS.sum_getD
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T08:42:10.635644+00:00
-- url     : https://prove2.me/theorems/adb1b5d6-66de-4133-809e-16ab481ff5dc
-- title:
--   OAI.NuclearUltrapower.SOS.sum_getD: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.SOS.sum_getD` of [lean/OAI/Analysis/NuclearUltrapower/SOSSemantics.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSSemantics.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS`):
--
--   ```lean
--   theorem sum_getD (N : ℕ) (p : List A) (h : p.length ≤ N) :
--       ((List.range N).map (fun i => p.getD i 0)).sum = p.sum
--   ```
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.SOS.eval_buckets` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSSemantics.lean (declaration OAI.NuclearUltrapower.SOS.sum_getD)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
section BucketSemantics
variable {α A β γ : Type*} [DecidableEq α] [AddCommGroup A]

omit [DecidableEq α] in
theorem sum_getD (N : ℕ) (p : List A) (h : p.length ≤ N) :
    ((List.range N).map (fun i => p.getD i 0)).sum = p.sum := by
  sorry

end BucketSemantics
end NuclearUltrapower.SOS

end

end OAI
end
