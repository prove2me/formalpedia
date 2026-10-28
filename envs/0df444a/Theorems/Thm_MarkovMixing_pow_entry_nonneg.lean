-- Prove2me | Theorems.Thm_MarkovMixing_pow_entry_nonneg
-- name    : MarkovMixing.pow_entry_nonneg
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T01:08:06.073358+00:00
-- url     : https://prove2.me/theorems/1ed484f3-6b2a-4d97-a9a1-b49ba757ccbf
-- title:
--   Every power of a stochastic matrix has nonnegative entries
-- statement:
--   Let $P$ be the transition matrix of a Markov chain on a finite state space $V$, so that
--   $P$ is stochastic: $P(x,y) \ge 0$ for all states and $\sum_y P(x,y) = 1$ for each $x$. Then every
--   power of $P$ has nonnegative entries:
--
--   $$
--   \bigl(P^{t}\bigr)(x,y) \;\ge\; 0 \qquad \text{for all } t \in \mathbb{N} \text{ and } x, y \in V .
--   $$
--
--   The entries of $P^t$ are the $t$-step transition probabilities, so this is the statement that
--   they are probabilities at all. It is the induction that every later estimate on $P^t$ silently
--   assumes — positivity of a path weight, monotonicity of a sum over intermediate states —
--   and it is needed before the stronger statement that some power is strictly positive.
-- source:
--   D. A. Levin, Y. Peres and E. L. Wilmer, Markov Chains and Mixing Times, 2nd ed., AMS 2017, §1.1; carved from the accepted proof of DiaconisStroock.Poincare.proposition_1, https://prove2.me/submissions/b36a2a77-0ed1-410e-b982-dafb4dc643a6

import Mathlib
import Definitions.Def_mm_spectral

open scoped BigOperators
open scoped Matrix
open MarkovMixing
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem MarkovMixing.pow_entry_nonneg {P : Matrix V V ℝ} (hP : IsStochastic P) :
    ∀ (t : ℕ) (x y : V), 0 ≤ (P ^ t) x y := by sorry
