-- Prove2me | Theorems.Thm_OAI_Erdos3_prepared_source_side_budgets
-- name    : OAI.Erdos3.prepared_source_side_budgets
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T10:15:52.498888+00:00
-- url     : https://prove2.me/theorems/dda8908f-cfb3-4c82-bad7-cb7b485353ab
-- title:
--   Large sides with bounded loss give lengths at least exp(required) and exp(-(p+2)^c)·N
-- statement:
--   Let $X$ be a type, $p$ and $\mathrm{required}$ real numbers, and $c,e$ natural numbers, with $2\le p$ and $\mathrm{required}\le (p+2)^e$. Let $N,\mathrm{length} : X\to\mathbb{N}$ satisfy, for every $i\in X$, $\exp\big((p+2)^{\max(c,e)+1}\big)\le N(i)$ and $N(i)\le \exp\big((p+2)^c\big)\cdot\mathrm{length}(i)$ (as real numbers). Then both of the following hold: for every $i$, $e^{\mathrm{required}}\le \mathrm{length}(i)$; and for every $i$, $\exp\big(-(p+2)^c\big)\cdot N(i)\le \mathrm{length}(i)$.
--
--   Lean: `OAI.Erdos3.prepared_source_side_budgets` in `lean/OAI/Combinatorics/Progressions/Dynamics/PreparedSourceSideBudget.lean` (OpenAI); the statement uses only Mathlib definitions.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/PreparedSourceSideBudget.lean#L46

import Mathlib
import Definitions.Def_ErdosReciprocal

namespace OAI

section

namespace Erdos3

theorem prepared_source_side_budgets {X : Type*} {p required : ℝ} {c e : ℕ}
    (hp : 2 ≤ p) (hrequired : required ≤ (p + 2) ^ e)
    (N length : X → ℕ)
    (hlarge : ∀ i, Real.exp ((p + 2) ^ (max c e + 1)) ≤ N i)
    (hloss : ∀ i, (N i : ℝ) ≤ Real.exp ((p + 2) ^ c) * length i) :
    (∀ i, Real.exp required ≤ (length i : ℝ)) ∧
      (∀ i, Real.exp (-((p + 2) ^ c)) * N i ≤ (length i : ℝ)) := by
  sorry

end Erdos3
end
end OAI
