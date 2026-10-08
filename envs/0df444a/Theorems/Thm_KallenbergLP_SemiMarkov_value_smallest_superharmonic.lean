-- Prove2me | Theorems.Thm_KallenbergLP_SemiMarkov_value_smallest_superharmonic
-- name    : KallenbergLP.SemiMarkov.value_smallest_superharmonic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:09:53.875153+00:00
-- url     : https://prove2.me/theorems/a7a0e201-651f-4b30-aca1-33fff8bb22de
-- title:
--   Theorem 7.2.1 — value is the smallest DRD-superharmonic vector
-- statement:
--   For the finite semi-Markov decision model under Assumption 7.2.1, let $v^\lambda_i$ be the supremum of discounted expected rewards over all history-dependent randomized policies starting at $i$. Then $v^\lambda$ is DRD-superharmonic, and every DRD-superharmonic vector $w$ lies above it coordinatewise:
--
--   $$
--   v^\lambda_i\geq r^*_{ia}+\sum_jp^*_{iaj}v^\lambda_j\quad(a\in A(i)),\qquad
--   w\text{ DRD-superharmonic}\Longrightarrow v^\lambda_i\leq w_i\quad(i\in E).
--   $$
--
--   This characterizes the optimal discounted value without restricting the policies in the supremum to stationary or Markov policies.
--
--   **Formalization Note** The state set is nonempty, and the strict transform bound is part of the discounted model. Both the value vector and the superharmonic comparison are real-valued.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 214, Theorem 7.2.1, https://ir.cwi.nl/pub/13008

import Mathlib
import Definitions.Def_KallenbergLP_SemiMarkov_Discounted

namespace KallenbergLP.SemiMarkov

variable {S U : Type*} [Fintype S] [Fintype U] [Nonempty S] [DecidableEq S] [DecidableEq U]

/-- Theorem 7.2.1. The DRD value vector satisfies every discounted Bellman
inequality and lies below every other vector that does. -/
theorem value_smallest_superharmonic (M : Discounted S U) :
    Superharmonic M (value M) ∧
      ∀ w : S → ℝ, Superharmonic M w → ∀ i : S, value M i ≤ w i := by sorry

end KallenbergLP.SemiMarkov
