-- Prove2me | Theorems.Thm_GaussianSweep_lemma_8_7
-- name    : GaussianSweep.lemma_8_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:54:47.86298+00:00
-- url     : https://prove2.me/theorems/5bcca118-f726-4df2-b044-99020a32d725
-- title:
--   Lemma 8.7 — $f_{3,r}(t) \le f_{3,r}(0)$ for $t \ge 0$
-- statement:
--   For every $r \in (0,1)$ and every $t \ge 0$,
--   $$
--   f_{3,r}(t) \le f_{3,r}(0),
--   $$
--   where $f_{3,r}$ is the ideal 3-star function. Among nonnegative thresholds the frontier probability of the ideal star is largest at the median $0$.
--
--   Differences from the source: none.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 8.7, p.50 (PDF p.52)

import Mathlib
import Definitions.Def_GaussianSweep_f3

namespace GaussianSweep

/-- Lemma 8.7 (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 8.7, p.50 (PDF p.52)). For every `r ∈ (0, 1)` and every `t ≥ 0`,
`f_{3,r}(t) ≤ f_{3,r}(0)`. -/
theorem lemma_8_7 (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (t : ℝ) (ht : 0 ≤ t) :
    f3 r t ≤ f3 r 0 := by sorry

end GaussianSweep
