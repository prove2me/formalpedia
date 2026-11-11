-- Prove2me | Theorems.Thm_LogLogJam_lemma_6_4
-- name    : LogLogJam.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:22:08.869777+00:00
-- url     : https://prove2.me/theorems/cb49fae9-cca1-4a01-966e-677398d7a5bd
-- title:
--   Lemma 6.4 — $f^{\circ t}(1/N)\le4N^{-2^{-t}}$ for $t\le\log_2\log_2N$
-- statement:
--   Let $N>1$, $f(x)=x+\sqrt x$, and let $t$ be a nonnegative integer with $t\le\log_2\log_2N$. Then
--
--   $$
--   f^{\circ t}(1/N)\le4N^{-2^{-t}} .
--   $$
--
--   Each application of $f$ at most square-roots the scale, so reaching a constant from $1/N$ takes about $\log_2\log_2N$ steps.
--
--   Differences from the source: none.
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), Lemma 6.4, p.33 (PDF p.36)

import Mathlib
import Definitions.Def_LogLogJam_fisherInfo

namespace LogLogJam

/-- **Lemma 6.4** (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, Lemma 6.4, p.33): "Let N > 1 and t be a nonnegative integer such that
t ≤ log₂ log₂ N, we have f^{∘t}(1/N) ≤ 4N^{−2^{−t}}." Here `f(x) = x + √x`. -/
theorem lemma_6_4 (N : ℝ) (hN : 1 < N) (t : ℕ) (ht : (t : ℝ) ≤ Real.logb 2 (Real.logb 2 N)) :
    fIter t (1 / N) ≤ 4 * N ^ (-(2 : ℝ) ^ (-(t : ℝ))) := by sorry

end LogLogJam
