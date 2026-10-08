-- Prove2me | Theorems.Thm_OAI_Erdos3_retained_core_allowance_spec
-- name    : OAI.Erdos3.retained_core_allowance_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T10:15:48.447053+00:00
-- url     : https://prove2.me/theorems/10c77796-3b59-4132-9177-d1e6c714306c
-- title:
--   ε/(2+ε) lies in (0,1] and times (2+ε) is at most ε
-- statement:
--   Let $\varepsilon$ be a real number with $0<\varepsilon$. Then $0<\varepsilon/(2+\varepsilon)$, $\varepsilon/(2+\varepsilon)\le 1$, and $\big(\varepsilon/(2+\varepsilon)\big)\cdot(2+\varepsilon)\le\varepsilon$.
--
--   Lean: `OAI.Erdos3.retained_core_allowance_spec` in `lean/OAI/Combinatorics/Progressions/Dynamics/NormalizedCoreBudget.lean` (OpenAI); the statement uses only Mathlib definitions.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/NormalizedCoreBudget.lean#L9

import Mathlib

namespace OAI

section

namespace Erdos3

theorem retained_core_allowance_spec {ε : ℝ} (hε : 0 < ε) :
    0 < ε / (2 + ε) ∧ ε / (2 + ε) ≤ 1 ∧ (ε / (2 + ε)) * (2 + ε) ≤ ε := by
  sorry

end Erdos3
end
end OAI
