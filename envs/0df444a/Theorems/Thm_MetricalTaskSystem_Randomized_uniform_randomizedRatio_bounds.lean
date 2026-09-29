-- Prove2me | Theorems.Thm_MetricalTaskSystem_Randomized_uniform_randomizedRatio_bounds
-- name    : MetricalTaskSystem.Randomized.uniform_randomizedRatio_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:21:39.154984+00:00
-- url     : https://prove2.me/theorems/7b5d983a-8153-4021-be68-f593d8b25d64
-- title:
--   Theorem 7.1 — $H(n)\le\bar w(S,d)\le 2H(n)$ for the uniform task system
-- statement:
--   Let $(S,d)$ be the uniform task system on $n$ states: every transition between distinct states costs $1$. Let $H(n)=1+\frac12+\cdots+\frac1n$ and let $\bar w(S,d)$ be the randomized competitive ratio (against an oblivious adversary). Then
--   $$H(n)\le\bar w(S,d)\le 2H(n).$$
--
--   Randomization thus lowers the competitive ratio of the uniform task system from $2n-1$ (the deterministic value) to $\Theta(\log n)$, determined up to a factor of $2$.
--
--   **Formalization Note** $\bar w(S,d)$ is the real infimum of the set of all $w$ for which some randomized on-line algorithm is expected $w$-competitive. The lower half forces this set to be nonempty (otherwise the infimum would be $0<H(n)$), so the conjunction is not vacuous. Tasks are finite and nonnegative; the paper also allows $+\infty$ entries. At $n=1$ the statement reads $1\le\bar w\le 2$.
-- source:
--   Borodin, Linial, Saks, An Optimal On-Line Algorithm for Metrical Task System, J. ACM 39(4) (1992), p. 759, Theorem 7.1

import Mathlib
import Definitions.Def_MetricalTaskSystem_Randomized_Model
import Definitions.Def_MetricalTaskSystem_Randomized_RandomizedAlgorithm

namespace MetricalTaskSystem.Randomized

/-- **Theorem 7.1** (Borodin–Linial–Saks 1992, p. 759). If `(S, d)` is the uniform task system on
`n = |S|` states, then `H(n) ≤ w̄(S, d) ≤ 2H(n)`, where `H(n) = 1 + 1/2 + ⋯ + 1/n` and `w̄` is the
randomized competitive ratio. -/
theorem uniform_randomizedRatio_bounds {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] :
    (harmonic (Fintype.card S) : ℝ) ≤ randomizedRatio (uniformD (S := S)) ∧
      randomizedRatio (uniformD (S := S)) ≤ 2 * (harmonic (Fintype.card S) : ℝ) := by sorry

end MetricalTaskSystem.Randomized
