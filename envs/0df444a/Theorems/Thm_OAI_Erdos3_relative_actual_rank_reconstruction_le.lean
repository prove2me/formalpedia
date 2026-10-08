-- Prove2me | Theorems.Thm_OAI_Erdos3_relative_actual_rank_reconstruction_le
-- name    : OAI.Erdos3.relative_actual_rank_reconstruction_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T10:16:02.114851+00:00
-- url     : https://prove2.me/theorems/c534d306-5eef-4e27-84b4-5d4502caca66
-- title:
--   d + s·removed is at most d₀ + s·old when d ≤ d₀ + s·(old − removed)
-- statement:
--   Let $s,d,d_0,\mathrm{old},\mathrm{removed}$ be natural numbers with $\mathrm{removed}\le\mathrm{old}$ and $d\le d_0+s\cdot(\mathrm{old}-\mathrm{removed})$ (natural-number subtraction, which here is the ordinary difference). Then $d+s\cdot\mathrm{removed}\le d_0+s\cdot\mathrm{old}$.
--
--   Lean: `OAI.Erdos3.relative_actual_rank_reconstruction_le` in `lean/OAI/Combinatorics/Progressions/Linear/RelativeActualRankBudget.lean` (OpenAI); the statement uses only Mathlib definitions.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/RelativeActualRankBudget.lean#L9

import Mathlib
import Definitions.Def_ErdosReciprocal

namespace OAI

section

namespace Erdos3

theorem relative_actual_rank_reconstruction_le
    {s d d₀ old removed : ℕ} (hremoved : removed ≤ old)
    (hreturned : d ≤ d₀ + s * (old - removed)) :
    d + s * removed ≤ d₀ + s * old := by
  sorry

end Erdos3
end
end OAI
