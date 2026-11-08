-- Prove2me | Theorems.Thm_GaussianSweep_lemma_8_6
-- name    : GaussianSweep.lemma_8_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:54:49.787723+00:00
-- url     : https://prove2.me/theorems/2b235f43-f080-4f53-9c28-de3d3db291d8
-- title:
--   Lemma 8.6 — $f_{3,r}(0) = \kappa(r)$
-- statement:
--   For every $r \in (0, 1)$,
--   $$
--   f_{3,r}(0) = \kappa(r) = \frac{3}{4\pi}\arccos\frac{3r^2-1}{2},
--   $$
--   where $f_{3,r}$ is the ideal 3-star function. At $r = r^* = 2\sqrt2/3$ this value is $c_3$.
--
--   Differences from the source: none.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 8.6, p.49 (PDF p.51)

import Mathlib
import Definitions.Def_GaussianSweep_f3
import Definitions.Def_GaussianSweep_kappa

namespace GaussianSweep

/-- Lemma 8.6 (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 8.6, p.49 (PDF p.51)). For every `r ∈ (0, 1)`, `f_{3,r}(0) = κ(r)`. -/
theorem lemma_8_6 (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) : f3 r 0 = kappa r := by sorry

end GaussianSweep
