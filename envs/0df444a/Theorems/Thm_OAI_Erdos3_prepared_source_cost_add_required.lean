-- Prove2me | Theorems.Thm_OAI_Erdos3_prepared_source_cost_add_required
-- name    : OAI.Erdos3.prepared_source_cost_add_required
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T10:15:58.868042+00:00
-- url     : https://prove2.me/theorems/47625a0e-d25a-4782-93cb-bbf352ad20a1
-- title:
--   (p+2)^c + required is at most (p+2)^(max c e + 1)
-- statement:
--   Let $p$ and $\mathrm{required}$ be real numbers and $c,e$ natural numbers, with $2\le p$ and $\mathrm{required}\le (p+2)^e$. Then
--   $$(p+2)^c+\mathrm{required}\le (p+2)^{\max(c,e)+1}.$$
--
--   Lean: `OAI.Erdos3.prepared_source_cost_add_required` in `lean/OAI/Combinatorics/Progressions/Dynamics/PreparedSourceSideBudget.lean` (OpenAI); the statement uses only Mathlib definitions.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/PreparedSourceSideBudget.lean#L18

import Mathlib
import Definitions.Def_ErdosReciprocal

namespace OAI

section

namespace Erdos3

theorem prepared_source_cost_add_required {p required : ℝ} {c e : ℕ}
    (hp : 2 ≤ p) (hrequired : required ≤ (p + 2) ^ e) :
    (p + 2) ^ c + required ≤ (p + 2) ^ (max c e + 1) := by
  sorry

end Erdos3
end
end OAI
