-- Prove2me | Theorems.Thm_KallenbergLP_Positive_value_smallest_nonnegative_superharmonic
-- name    : KallenbergLP.Positive.value_smallest_nonnegative_superharmonic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:05:15.451618+00:00
-- url     : https://prove2.me/theorems/6889d43e-289c-47c1-97f3-ff016c85831a
-- title:
--   Theorem 3.5.1 — the value is the smallest nonnegative TMD superharmonic vector
-- statement:
--   Suppose the finite Markov decision system has nonnegative rewards $r_{ia}\ge0$ for all admissible actions. Let $v_i=\sup_{R\in C}v_i(R)$ be the total reward value, allowing $+\infty$.
--
--   Then $v$ is nonnegative, satisfies the extended superharmonic inequalities
--   $$
--   v_i\ge r_{ia}+\sum_{j\in E}p_{iaj}v_j\qquad(i\in E,\ a\in A(i)),
--   $$
--   and is no larger, componentwise, than every nonnegative real TMD superharmonic vector $w$.
--
--   This identifies the value as the least superharmonic upper bound and justifies the primal linear program (3.5.1). The original Definition 3.3.1 makes $w$ real valued; $v$ may have an infinite component.
--
--   **Formalization Note** The extended sum uses $0\cdot(+\infty)=0$, as in Definition 3.2.1. All terms are nonnegative, so the ambiguous sum $(+\infty)+(-\infty)$ cannot occur.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 78 (PDF p. 86), Theorem 3.5.1; p. 52 (PDF p. 60), Definition 3.3.1; p. 39 (PDF p. 47), Definition 3.2.1

import Definitions.Def_KallenbergLP_Positive_Value

namespace KallenbergLP.Positive

/-- Theorem 3.5.1: the extended value is nonnegative and satisfies the
Bellman superharmonic inequalities; every nonnegative real superharmonic
vector is an upper bound. -/
theorem value_smallest_nonnegative_superharmonic
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α] (M : MDP N α)
    (hr : ∀ i a, a ∈ M.actions i → 0 ≤ M.reward i a) :
    (∀ i : Fin N, (0 : EReal) ≤ value M i) ∧
    (∀ i (a : α), a ∈ M.actions i →
      (↑(M.reward i a) : EReal) +
        ∑ j : Fin N, (↑(M.transition i a j) : EReal) * value M j ≤ value M i) ∧
    (∀ w : Fin N → ℝ, (∀ i, 0 ≤ w i) → IsSuperharmonic M w →
      ∀ i, value M i ≤ (↑(w i) : EReal)) := by sorry

end KallenbergLP.Positive
