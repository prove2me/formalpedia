-- Prove2me | Theorems.Thm_OAI_Erdos3_integerIntervalBox_window_factor_le
-- name    : OAI.Erdos3.integerIntervalBox_window_factor_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T10:45:50.440669+00:00
-- url     : https://prove2.me/theorems/48aa9312-59ec-4675-8f6e-6f2241d1dccf
-- title:
--   3^|I|·∏S_i divided by the box size is at most (3K)^|I|
-- statement:
--   Let $I$ be a finite type with decidable equality, and $\mathrm{lo},\mathrm{hi} : I\to\mathbb{Z}$ with $\mathrm{lo}_i<\mathrm{hi}_i$ for every $i$. Let $S : I\to\mathbb{R}$ satisfy $0\le S_i$ for every $i$, and let $K$ be a real number with $S_i\le K\,(\mathrm{hi}_i-\mathrm{lo}_i)$ for every $i$. Let $Q$ be the finite box $\prod_{i\in I}\big([\mathrm{lo}_i,\mathrm{hi}_i)\cap\mathbb{Z}\big)\subseteq\mathbb{Z}^I$. Then
--   $$\frac{3^{|I|}\prod_{i\in I}S_i}{|Q|}\le (3K)^{|I|}.$$
--
--   Lean: `OAI.Erdos3.integerIntervalBox_window_factor_le` in `lean/OAI/Combinatorics/Progressions/Lattices/IntegerWindowFactor.lean` (OpenAI); the statement uses only Mathlib definitions.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/IntegerWindowFactor.lean#L20

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B010

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem integerIntervalBox_window_factor_le {I : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (hlen : ∀ i, lo i < hi i)
    (S : I → ℝ) (hS : ∀ i, 0 ≤ S i) {K : ℝ}
    (hside : ∀ i, S i ≤ K * ((hi i - lo i : ℤ) : ℝ)) :
    (3 : ℝ) ^ Fintype.card I * (∏ i, S i) /
      (Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i))).card ≤
        (3 * K) ^ Fintype.card I := by
  sorry

end Erdos3
end
end OAI
