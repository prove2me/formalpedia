-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_eval_mul
-- name    : OAI.NuclearUltrapower.SOS.eval_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T08:42:18.79499+00:00
-- url     : https://prove2.me/theorems/12d3c407-b0f5-4dfb-b5f4-694c4b58d994
-- title:
--   OAI.NuclearUltrapower.SOS.eval_mul: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.SOS.eval_mul` of [lean/OAI/Analysis/NuclearUltrapower/SOSSemantics.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSSemantics.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS`):
--
--   ```lean
--   theorem eval_mul (f : α → A) (μ : α → α → α) (ps qs : Poly α)
--       (h : ∀ p ∈ ps, ∀ q ∈ qs, f (μ p.1 q.1) = f p.1 * f q.1) :
--       eval f (ps.flatMap (fun p => qs.map (fun q => (μ p.1 q.1, p.2*q.2)))) =
--         eval f ps * eval f qs
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SOS.Poly` and `OAI.NuclearUltrapower.SOS.eval` (definitions bundle `OAIQ019N000` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.SOS.residual_value_generic` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSSemantics.lean (declaration OAI.NuclearUltrapower.SOS.eval_mul)

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
theorem eval_mul (f : α → A) (μ : α → α → α) (ps qs : Poly α)
    (h : ∀ p ∈ ps, ∀ q ∈ qs, f (μ p.1 q.1) = f p.1 * f q.1) :
    eval f (ps.flatMap (fun p => qs.map (fun q => (μ p.1 q.1, p.2*q.2)))) =
      eval f ps * eval f qs := by
  sorry
end EvalOperations
end NuclearUltrapower.SOS

end

end OAI
end
