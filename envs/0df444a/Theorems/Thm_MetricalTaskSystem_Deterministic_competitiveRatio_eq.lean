-- Prove2me | Theorems.Thm_MetricalTaskSystem_Deterministic_competitiveRatio_eq
-- name    : MetricalTaskSystem.Deterministic.competitiveRatio_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:16:03.322342+00:00
-- url     : https://prove2.me/theorems/dc8b5fae-89f4-4bfa-b188-2a48f8966160
-- title:
--   Theorem 1.1 — every $n$-state metrical task system has competitive ratio $w(S,d)=2n-1$
-- statement:
--   Let $(S,d)$ be a metrical task system with $n\ge1$ states: $d(i,i)=0$, $d(i,j)=d(j,i)>0$ for $i\neq j$, and $d$ satisfies the triangle inequality. Then its competitive ratio, the infimum over all deterministic on-line algorithms $A$ of the infimum of all $w$ for which $A$ is $w$-competitive, equals
--   $$w(S,d)=2n-1 .$$
--
--   In particular the optimal competitive ratio depends only on the number of states, not on the distances.
--
--   **Formalization Note** Tasks are finite and nonnegative (the paper also allows $+\infty$ entries; these are excluded, which affects neither bound). The competitive ratio is the real infimum of all $w$ for which some on-line algorithm is $w$-competitive; since the right-hand side is at least $1$, the statement also asserts that some algorithm is competitive. At $n=1$ the statement is the true claim $w(S,d)=1$.
-- source:
--   Borodin, Linial, Saks, An Optimal On-Line Algorithm for Metrical Task System, J. ACM 39(4) (1992), p. 747, Theorem 1.1

import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model

namespace MetricalTaskSystem.Deterministic

/-- **Theorem 1.1** (Borodin–Linial–Saks 1992, p. 747). For any metrical task system `(S, d)`
with `n` states, the competitive ratio is `w(S, d) = 2n − 1`. -/
theorem competitiveRatio_eq {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (d : S → S → ℝ) (hd : IsMetrical d) :
    competitiveRatio d = 2 * (Fintype.card S : ℝ) - 1 := by sorry

end MetricalTaskSystem.Deterministic
