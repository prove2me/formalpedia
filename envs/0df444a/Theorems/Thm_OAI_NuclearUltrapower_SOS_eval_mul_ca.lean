-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_eval_mul_ca
-- name    : OAI.NuclearUltrapower.SOS.eval_mul_ca
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T15:01:05.788808+00:00
-- url     : https://prove2.me/theorems/8f961231-4147-4c4c-b43d-324aa3425420
-- title:
--   OAI.NuclearUltrapower.SOS.eval_mul_ca: intermediate lemma from OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS`):
--
--   ```lean
--   theorem eval_mul_ca (f : α → A) (μ : α → α → α) (ps qs : Poly α)
--       (h : ∀ p ∈ ps, ∀ q ∈ qs, f (μ p.1 q.1) = f p.1 * f q.1) :
--       eval f (ps.flatMap (fun p => qs.map (fun q => (μ p.1 q.1, p.2*q.2)))) =
--         eval f ps * eval f qs
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SOS.Poly` and `OAI.NuclearUltrapower.SOS.eval` (definitions bundle `OAIQ229C003` of this split).
--
--   **Used by.** The proofs of `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_certificate_ca` and `OAI_NuclearUltrapower_SOS_residual_value_generic_ca` of this split import it.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ229C003

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
theorem eval_mul_ca (f : α → A) (μ : α → α → α) (ps qs : Poly α)
    (h : ∀ p ∈ ps, ∀ q ∈ qs, f (μ p.1 q.1) = f p.1 * f q.1) :
    eval f (ps.flatMap (fun p => qs.map (fun q => (μ p.1 q.1, p.2*q.2)))) =
      eval f ps * eval f qs := by
  sorry
end EvalOperations
end NuclearUltrapower.SOS

end

end OAI
end
