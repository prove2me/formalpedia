-- Prove2me | Theorems.Thm_KingmanSubadditive_Ulam_theorem_8_lower_bound
-- name    : KingmanSubadditive.Ulam.theorem_8_lower_bound
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-06T17:37:15.104929+00:00
-- url     : https://prove2.me/theorems/0c791756-7a51-454b-a20e-51788b20b0fc
-- title:
--   Theorem 8, lower half of (2.4.4) — the Ulam constant satisfies $c \ge (8/\pi)^{1/2}$
-- statement:
--   Let $c$ be the constant of (2.4.3), that is, the limit in probability of $n^{-1/2}\,l(\pi_n)$ for $\pi_n$ uniformly distributed over the permutation group $\mathcal S_n$, where $l(\pi_n)$ is the length of the longest ascending sequence (Theorem 7). Then
--   $$c \ \ge\ \Big(\frac8\pi\Big)^{1/2}.$$
--
--   This is the left inequality of (2.4.4) in Theorem 8. Kingman obtains it from Hammersley's construction: in a planar Poisson process of unit rate, a greedy ascending path has i.i.d. increments whose mean is $\int_0^\infty\int_0^\infty x e^{-\frac12(x+y)^2}\,dx\,dy = (\pi/8)^{1/2}$, which yields the lower bound on $c$.
--
--   **Formalization Note** As in Theorem 8, the constant enters as the hypothesis that $n^{-1/2}l(\pi_n)$ converges in probability to $c$ (`ConvergesInProbUniform c`); no sign or bound on $c$ is assumed. $\pi$ in the bound is the circle constant.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, §2.4, Theorem 8, left inequality of (2.4.4), proved on p. 895

import Mathlib
import Definitions.Def_KingmanSubadditive_Ulam_Permutations

namespace KingmanSubadditive.Ulam

/-- **Lower bound of (2.4.4)** (Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899
(1973), §2.4, Theorem 8 and the first part of its proof, p. 895). The constant `c` in (2.4.3),
the limit in probability of `n^{−½} l(π_n)` for `π_n` uniform on `𝒮_n`, satisfies
`(8/π)^½ ≤ c`.

**Formalization Note** As in Theorem 8, the constant enters as the hypothesis
`ConvergesInProbUniform c`; no sign or bound on `c` is assumed. -/
theorem theorem_8_lower_bound (c : ℝ) (hc : ConvergesInProbUniform c) :
    Real.sqrt (8 / Real.pi) ≤ c := by sorry

end KingmanSubadditive.Ulam
