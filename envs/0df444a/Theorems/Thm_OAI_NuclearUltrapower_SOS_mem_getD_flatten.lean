-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_mem_getD_flatten
-- name    : OAI.NuclearUltrapower.SOS.mem_getD_flatten
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T07:55:44.636359+00:00
-- url     : https://prove2.me/theorems/871f1b11-c6e0-4f10-943d-ca06a1019705
-- title:
--   OAI.NuclearUltrapower.SOS.mem_getD_flatten: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.SOS.mem_getD_flatten` of [lean/OAI/Analysis/NuclearUltrapower/IntegralCertificate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/IntegralCertificate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS`):
--
--   ```lean
--   theorem mem_getD_flatten {a : α} (rs : List (List α)) (n : ℕ) (h : a ∈ rs.getD n []) :
--       a ∈ rs.flatten
--   ```
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.SOS.bucket_support_original` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/IntegralCertificate.lean (declaration OAI.NuclearUltrapower.SOS.mem_getD_flatten)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace NuclearUltrapower.SOS
variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem mem_getD_flatten {a : α} (rs : List (List α)) (n : ℕ) (h : a ∈ rs.getD n []) :
    a ∈ rs.flatten := by
  sorry

end NuclearUltrapower.SOS

end

end OAI
end
