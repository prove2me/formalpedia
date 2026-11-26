-- Prove2me | Theorems.Thm_OddPerfectNumber_nielsen_calibration_prod
-- name    : OddPerfectNumber.nielsen_calibration_prod
-- status  : Proved
-- author  : @curiyu
-- created : 2026-09-08T04:10:16.809763+00:00
-- url     : https://prove2.me/theorems/80a95a32-85a8-4476-b554-c45f42198cf7
-- title:
--   Nielsen calibration product $\\prod (1-1/n_i) = a/(a+1)$
-- statement:
--   This is the calibrating product identity behind Lemma 1 of Nielsen 2003 (Section 2), in the form made explicit as equation (11) of the 2024 exposition.
--
--   Let $a \ge 1$ and $r \ge 1$ be integers, and put $A = a+1$. Consider the calibrating integers $n_i = A^{2^{i-1}} + 1$ for $1 \le i < r$ together with $n_r = A^{2^{r-1}}$. Then
--   $$
--   \prod_{i=1}^{r}\left(1-\frac{1}{n_i}\right) = \frac{a}{a+1}.
--   $$
--   The identity is a telescoping consequence of the factorization $A^{2^{m}} - 1 = (A-1)\prod_{i<m}(A^{2^{i}}+1)$. In the paper this sequence is the extremal example: it satisfies the hypothesis $(*)$ of Lemma 1 with equality on the left, and Cook's comparison lemma shows every other admissible tuple has partial products dominating it, which is how the maximality argument in Lemma 1 gets off the ground.
--
--   **Formalization Note** The sequence is $0$-indexed in Lean; the product is split into the first $r-1$ factors over `Finset.range (r - 1)` and the distinguished last factor, and all divisions are in $\mathbb{Q}$ with explicit casts.
-- source:
--   P. P. Nielsen, An upper bound for odd perfect numbers, INTEGERS 3 (2003), #A14, Section 2 (ni construction); see also equation (11) of the 2024 exposition, https://math.colgate.edu/~integers/y114/y114.pdf

import Mathlib
open BigOperators Finset

namespace OddPerfectNumber

theorem nielsen_calibration_prod (a r : ℕ) (ha : 0 < a) (hr : 0 < r) :
    (∏ i ∈ Finset.range (r - 1), (1 - 1 / (((a + 1) ^ (2 ^ i) + 1 : ℕ) : ℚ))) *
      (1 - 1 / ((((a + 1) ^ (2 ^ (r - 1)) : ℕ)) : ℚ)) =
      ((a : ℕ) : ℚ) / (((a : ℕ) : ℚ) + 1) := by
  sorry

end OddPerfectNumber
