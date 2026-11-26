-- Prove2me | Theorems.Thm_LL_PV420Split1122_pomerance_sec4
-- name    : LL_PV420Split1122.pomerance_sec4
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-26T20:40:32.324297+00:00
-- url     : https://prove2.me/theorems/a4cb92aa-a331-4750-b402-ed2902603877
-- title:
--   Pomerance's Section 4 bound: $\sum_{m\le n}|\cos m\alpha-\cos m\beta|/m<\log n+\gamma+\log 2+3/n$
-- statement:
--   For all real numbers $\alpha,\beta$ and every integer $n\ge1$, $\sum_{m=1}^{n}|\cos(m\alpha)-\cos(m\beta)|/m<\log n+\gamma+\log 2+3/n$, where $\gamma$ is the Euler-Mascheroni constant.
-- source:
--   C. Pomerance, Integers 11A, 2011, Article 19, Section 4; Frolenkov, arXiv 1107.0381, Lemma 2.

import Mathlib

open Real Finset

namespace LL_PV420Split1122
theorem pomerance_sec4 (α β : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ m ∈ Icc 1 n, |cos (m * α) - cos (m * β)| / m <
      log n + eulerMascheroniConstant + log 2 + 3 / n := by sorry
end LL_PV420Split1122
