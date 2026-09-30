-- Prove2me | Theorems.Thm_NonuniformCompetitive_Snoopy_ratio_attained
-- name    : NonuniformCompetitive.Snoopy.ratio_attained
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:49:44.670278+00:00
-- url     : https://prove2.me/theorems/80b2d923-6a7d-42a5-87dd-1f7e40d04e62
-- title:
--   Theorem 4 (second claim) — a randomized snoopy-caching algorithm is $e_p/(e_p-1)$-competitive
-- statement:
--   Consider the single-block snoopy-caching task system with $n$ processors and block-transfer cost $p \ge 1$ (block size $p-1$), and fix any initial state $s_0$. There is a randomized on-line algorithm $A$, all of whose deterministic components start in $s_0$, and a constant $a$ such that for every admissible request sequence $\sigma$,
--
--   $$\mathbf{E}C_A(\sigma) \le \frac{e_p}{e_p - 1}\cdot C_{opt}(s_0,\sigma) + a, \qquad e_p = \left(1 + \frac1p\right)^p .$$
--
--   This is the attainment half of Theorem 4: randomization improves on the optimal deterministic ratio $2$ for every $p \ge 2$.
--
--   **Formalization Note** No lower bound on $n$ is assumed; for $n \le 1$ the statement holds trivially. The paper's algorithm is a mixture of threshold algorithms (make the block private after a random number of consecutive writes), but the statement only asserts existence.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), p. 551, Theorem 4, second claim (attainment); proof pp. 553–554

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_ep
import Definitions.Def_NonuniformCompetitive_Snoopy_model
import Definitions.Def_NonuniformCompetitive_Snoopy_randomized

namespace NonuniformCompetitive.Snoopy

/-- Theorem 4, second claim (Karlin et al. 1994, p. 551): in the single-block snoopy-caching
task system with `n` processors and block-transfer cost `p ≥ 1`, from every initial state `s₀`
there is a randomized on-line algorithm that is `e_p / (e_p − 1)`-competitive against an
oblivious adversary on admissible request sequences. -/
theorem ratio_attained (n p : ℕ) (hp : 1 ≤ p) (s₀ : State n) :
    ∃ A : RandomizedAlgorithm n p, A.IsCompetitiveFrom s₀ (ep p / (ep p - 1)) := by sorry

end NonuniformCompetitive.Snoopy
