-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_eval_buckets_ca
-- name    : OAI.NuclearUltrapower.SOS.eval_buckets_ca
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T17:43:57.100149+00:00
-- url     : https://prove2.me/theorems/6ac5cf54-4b4b-4bbb-a01c-1fc83d1ef971
-- title:
--   OAI.NuclearUltrapower.SOS.eval_buckets_ca: intermediate lemma from OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS`):
--
--   ```lean
--   theorem eval_buckets_ca (n : ℕ) (rs : List (List (Poly α)))
--       (h : ∀ r ∈ rs, r.length ≤ n) (f : α → A) (le : α → α → Bool) :
--       eval f ((List.range n).flatMap (fun b => normalize le (rs.flatMap (fun r => r.getD b [])))) =
--         eval f (rs.flatMap List.flatten)
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SOS.Poly` and `OAI.NuclearUltrapower.SOS.eval` (definitions bundle `OAIQ229C003` of this split); `OAI.NuclearUltrapower.SOS.normalize` (definitions bundle `OAIQ229C015` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.SOS.residual_eval_ca` of this split imports it.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ229C015

section

attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
section BucketSemantics
variable {α A β γ : Type*} [DecidableEq α] [AddCommGroup A]

theorem eval_buckets_ca (n : ℕ) (rs : List (List (Poly α)))
    (h : ∀ r ∈ rs, r.length ≤ n) (f : α → A) (le : α → α → Bool) :
    eval f ((List.range n).flatMap (fun b => normalize le (rs.flatMap (fun r => r.getD b [])))) =
      eval f (rs.flatMap List.flatten) := by
  sorry

end BucketSemantics
end NuclearUltrapower.SOS

end

end OAI
end
