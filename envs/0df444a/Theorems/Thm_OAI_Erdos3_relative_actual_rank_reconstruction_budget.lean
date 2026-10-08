-- Prove2me | Theorems.Thm_OAI_Erdos3_relative_actual_rank_reconstruction_budget
-- name    : OAI.Erdos3.relative_actual_rank_reconstruction_budget
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T10:15:52.820006+00:00
-- url     : https://prove2.me/theorems/d4970379-bff0-4fd7-8bbe-56892ba9b834
-- title:
--   d + s·removed is at most childCost + s·p
-- statement:
--   Let $s,d,\mathrm{removed},\mathrm{bound}$ be natural numbers and $\mathrm{childCost},p$ real numbers, with $0\le \mathrm{childCost}$, $d\le\min(\mathrm{bound},\lfloor\mathrm{childCost}\rfloor)$ (the natural-number floor), and $\mathrm{removed}\le p$. Then, with the natural number $d+s\cdot\mathrm{removed}$ cast to $\mathbb{R}$,
--   $$d+s\cdot\mathrm{removed}\le \mathrm{childCost}+s\cdot p.$$
--
--   Lean: `OAI.Erdos3.relative_actual_rank_reconstruction_budget` in `lean/OAI/Combinatorics/Progressions/Linear/RelativeActualRankBudget.lean` (OpenAI); the statement uses only Mathlib definitions.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/RelativeActualRankBudget.lean#L19

import Mathlib
import Definitions.Def_ErdosReciprocal

namespace OAI

section

namespace Erdos3

theorem relative_actual_rank_reconstruction_budget
    {s d removed bound : ℕ} {childCost p : ℝ}
    (hchild : 0 ≤ childCost) (hd : d ≤ min bound ⌊childCost⌋₊)
    (hremoved : (removed : ℝ) ≤ p) :
    ((d + s * removed : ℕ) : ℝ) ≤ childCost + (s : ℝ) * p := by
  sorry

end Erdos3
end
end OAI
