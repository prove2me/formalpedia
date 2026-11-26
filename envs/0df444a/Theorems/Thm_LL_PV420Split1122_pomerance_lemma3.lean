-- Prove2me | Theorems.Thm_LL_PV420Split1122_pomerance_lemma3
-- name    : LL_PV420Split1122.pomerance_lemma3
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-26T20:40:51.954784+00:00
-- url     : https://prove2.me/theorems/baacf5ae-26f3-49f3-bf9b-83025d2c4285
-- title:
--   Pomerance's Lemma 3: $\sum_{j\le n}|\sin jx|/j<\frac{2}{\pi}\log n+\frac{2}{\pi}(\gamma+\log 2+3/n)$
-- statement:
--   For every real number $x$ and every integer $n\ge1$, $\sum_{j=1}^{n}|\sin(jx)|/j<\frac{2}{\pi}\log n+\frac{2}{\pi}\bigl(\gamma+\log 2+3/n\bigr)$, where $\gamma$ is the Euler-Mascheroni constant.
-- source:
--   C. Pomerance, Integers 11A, 2011, Article 19, Lemma 3; Frolenkov, arXiv 1107.0381, Lemma 1.

import Mathlib

open Real Finset

namespace LL_PV420Split1122
theorem pomerance_lemma3 (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Icc 1 n, |sin (j * x)| / j <
      2 / π * log n + 2 / π * (eulerMascheroniConstant + log 2 + 3 / n) := by sorry
end LL_PV420Split1122
