-- Prove2me | Theorems.Thm_MetricalTaskSystem_Randomized_uniform_expCompetitive_two_harmonic
-- name    : MetricalTaskSystem.Randomized.uniform_expCompetitive_two_harmonic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:18:21.464532+00:00
-- url     : https://prove2.me/theorems/938fa9f0-4137-4cef-9fd8-e74c43cc3625
-- title:
--   Theorem 7.1 (upper bound) — an expected $2H(n)$-competitive randomized algorithm for the uniform task system
-- statement:
--   Let $(S,d)$ be the uniform task system on $n$ states (every transition costs $1$) and let
--   $$H(n)=1+\frac12+\frac13+\cdots+\frac1n .$$
--   There is a randomized on-line algorithm $R$ and a constant $K$ such that, for every initial state $s_0$ and every finite sequence $\mathbf T$ of nonnegative tasks,
--   $$\bar c_R(\mathbf T)\le 2H(n)\,c_0(\mathbf T)+K .$$
--
--   This is the upper half of Theorem 7.1: it shows $\bar w(S,d)\le 2H(n)$, a logarithmic ratio, whereas every deterministic on-line algorithm has competitive ratio at least $2n-1$.
--
--   **Formalization Note** The statement is the existence of an expected $2H(n)$-competitive algorithm, not the inequality $\bar w(S,d)\le 2H(n)$ alone, which would hold trivially if no algorithm were competitive (the real infimum of the empty set is $0$). Tasks are finite and nonnegative.
-- source:
--   Borodin, Linial, Saks, An Optimal On-Line Algorithm for Metrical Task System, J. ACM 39(4) (1992), p. 759, Theorem 7.1 and Proof of the Upper Bound

import Mathlib
import Definitions.Def_MetricalTaskSystem_Randomized_Model
import Definitions.Def_MetricalTaskSystem_Randomized_RandomizedAlgorithm

namespace MetricalTaskSystem.Randomized

/-- **Theorem 7.1, upper bound** (Borodin–Linial–Saks 1992, p. 759). On the uniform task system
with `n = |S|` states there is a randomized on-line algorithm that is expected
`2H(n)`-competitive, where `H(n) = 1 + 1/2 + ⋯ + 1/n`. -/
theorem uniform_expCompetitive_two_harmonic {S : Type} [Fintype S] [DecidableEq S]
    [Nonempty S] :
    ∃ R : RandomizedOnlineAlgorithm S,
      IsExpCompetitive (uniformD (S := S)) R (2 * (harmonic (Fintype.card S) : ℝ)) := by sorry

end MetricalTaskSystem.Randomized
