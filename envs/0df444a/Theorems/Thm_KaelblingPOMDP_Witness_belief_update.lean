-- Prove2me | Theorems.Thm_KaelblingPOMDP_Witness_belief_update
-- name    : KaelblingPOMDP.Witness.belief_update
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:48.192992+00:00
-- url     : https://prove2.me/theorems/635a88b5-8f9c-4563-b4b8-8a596d02a9e1
-- title:
--   §3.3, p. 107 — Pr(o | a, b) is a distribution over observations and SE(b, a, o) is a belief state
-- statement:
--   Let $\langle S, A, T, R, \Omega, O\rangle$ be a POMDP satisfying the standing hypotheses, let $b$ be a belief state and $a$ an action. With
--   $$\Pr(o \mid a, b) = \sum_{s'} O(s', a, o) \sum_{s} T(s, a, s')\, b(s),$$
--   we have:
--
--   1. $\Pr(o \mid a, b) \ge 0$ for every observation $o$;
--   2. $\sum_{o \in \Omega} \Pr(o \mid a, b) = 1$;
--   3. if $\Pr(o \mid a, b) \ne 0$, then the updated belief $SE(b, a, o)$, with $SE(b, a, o)(s') = O(s', a, o) \sum_s T(s, a, s') b(s) / \Pr(o \mid a, b)$, is a belief state.
--
--   The denominator of the state estimator is thus a normalizing factor that makes the new belief sum to one. This is what allows the Q-function of p. 114 to be written in terms of the values of updated belief states.
--
--   **Formalization Note** Belief states are the points of `stdSimplex ℝ S`. The case $\Pr(o \mid a, b) = 0$ is excluded in (3) because Lean's division by zero returns the zero vector.
-- source:
--   Kaelbling, Littman, Cassandra, Planning and acting in partially observable stochastic domains, Artificial Intelligence 101:99–134 (1998), DOI 10.1016/S0004-3702(98)00023-X, p. 107, §3.3, display of b′(s′)

import Mathlib
import Definitions.Def_KaelblingPOMDP_Witness_Useful

namespace KaelblingPOMDP.Witness

open Finset

universe u

/-- §3.3, p. 107 (Kaelbling, Littman, Cassandra, *Planning and acting in partially observable stochastic domains*,
Artificial Intelligence 101:99–134 (1998)): the normalizing factor `Pr(o | a, b)` of the state estimator is a
probability distribution over observations, and when `Pr(o | a, b) ≠ 0` the updated belief
`SE(b, a, o)` is again a belief state ("The denominator, Pr(o | a, b), can be treated as a
normalizing factor, independent of s′, that causes b′ to sum to 1").

**Formalization Note** Belief states are the points of `stdSimplex ℝ S`. When `Pr(o | a, b) = 0`
the formula divides by zero and Lean returns the zero vector, so that case is excluded. -/
theorem belief_update {S A Ω : Type u} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A] [DecidableEq A]
    [Nonempty A] [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (M : POMDP S A Ω) (hM : M.IsValid) (b : S → ℝ) (hb : b ∈ stdSimplex ℝ S) (a : A) :
    (∀ o, 0 ≤ obsProb M b a o) ∧ ∑ o, obsProb M b a o = 1 ∧
      ∀ o, obsProb M b a o ≠ 0 → stateEstimator M b a o ∈ stdSimplex ℝ S := by sorry

end KaelblingPOMDP.Witness
