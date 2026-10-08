-- Prove2me | Theorems.Thm_KVVMatching_UpperBound_lemma_16
-- name    : KVVMatching.UpperBound.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:16:05.98879+00:00
-- url     : https://prove2.me/theorems/8403decd-7c5c-4509-ab49-d195ff6e8f80
-- title:
--   Lemma 16 — asymptotic value of RANDOM on the triangular instance
-- statement:
--   Let $T_n$ be the $n\times n$ complete upper-triangular graph. The expected matching size of RANDOM on $T_n$ is $n(1-1/e)+o(n)$, in the two-sided sense
--
--   $$\lim_{n\to\infty}\frac{V_{T_n}(n,\varnothing)}{n}=1-e^{-1}.$$
--
--   This supplies the asymptotic value used in Theorem 2.
--
--   **Formalization Note** The paper writes $o(n)$ without a numerical rate. The value at $n=0$ is defined by Lean's total division but does not affect the limit.
-- source:
--   Karp, Vazirani, Vazirani, An Optimal Algorithm for On-line Bipartite Matching, STOC 1990, p. 357, Lemma 16

import Mathlib
import Definitions.Def_KVVMatching_UpperBound_RandomValue
import Definitions.Def_KVVMatching_UpperBound_Triangular

namespace KVVMatching.UpperBound

/-- Karp, Vazirani and Vazirani, Lemma 16 (p. 357). -/
theorem lemma_16 :
    Filter.Tendsto
      (fun n : ℕ => randomValue (upperTriangular n) / (n : ℝ))
      Filter.atTop (nhds (1 - Real.exp (-1))) := by sorry

end KVVMatching.UpperBound
