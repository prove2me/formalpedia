-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_sum_getD_ca
-- name    : OAI.NuclearUltrapower.SOS.sum_getD_ca
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T02:08:50.099636+00:00
-- url     : https://prove2.me/theorems/6c7ddf25-2fc8-47ec-8113-7859c1ef65f7
-- title:
--   OAI.NuclearUltrapower.SOS.sum_getD_ca: intermediate lemma from OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS`):
--
--   ```lean
--   theorem sum_getD_ca (N : ℕ) (p : List A) (h : p.length ≤ N) :
--       ((List.range N).map (fun i => p.getD i 0)).sum = p.sum
--   ```
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.SOS.eval_buckets_ca` of this split imports it.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0)

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
theorem sum_getD_ca (N : ℕ) (p : List A) (h : p.length ≤ N) :
    ((List.range N).map (fun i => p.getD i 0)).sum = p.sum := by
  sorry

end BucketSemantics
end NuclearUltrapower.SOS

end

end OAI
end
