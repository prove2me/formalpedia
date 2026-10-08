-- Prove2me | Theorems.Thm_KaelblingPOMDP_Witness_Q_function
-- name    : KaelblingPOMDP.Witness.Q_function
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:13:32.157008+00:00
-- url     : https://prove2.me/theorems/798466c6-c9ce-4e05-b16c-175aaa332cf8
-- title:
--   §4.4, p. 114 — Q^a_t(b) is the best value of an a-rooted tree, attained on the candidates, and V_t(b) = max_a Q^a_t(b)
-- statement:
--   Let $\langle S, A, T, R, \Omega, O\rangle$ be a POMDP satisfying the standing hypotheses, $t \ge 2$, $a$ an action and $b$ a belief state. Let
--   $$Q^a_t(b) = \sum_{s \in S} b(s) R(s, a) + \gamma \sum_{o \in \Omega} \Pr(o \mid a, b)\, V_{t-1}(SE(b, a, o)).$$
--   Then:
--
--   1. $Q^a_t(b)$ is the maximum of $V_p(b)$ over all $t$-step policy trees $p$ with root action $a$;
--   2. $Q^a_t(b)$ is also the maximum of $V_p(b)$ over the candidate set $C^a_t$ of $t$-step trees with root $a$ and every subtree in $\mathcal V_{t-1}$;
--   3. $V_t(b) = \max_{a} Q^a_t(b)$.
--
--   So $Q^a_t(b)$ is the value of taking action $a$ in belief state $b$ and continuing optimally for $t-1$ steps, and it can be computed by one-step lookahead using the useful $(t-1)$-step trees. This links the Q-function of the paper to the candidate trees from which the witness algorithm builds $\mathcal Q^a_t$.
--
--   **Formalization Note** Maxima in (1) and (2) are stated with `IsGreatest`, which includes that the maximum is attained. The term of an observation with $\Pr(o \mid a, b) = 0$ is multiplied by zero. Here $t = n + 2$.
-- source:
--   Kaelbling, Littman, Cassandra, Planning and acting in partially observable stochastic domains, Artificial Intelligence 101:99–134 (1998), DOI 10.1016/S0004-3702(98)00023-X, p. 114, §4.4, display of Q^a_t(b) and V_t(b) = max_a Q^a_t(b)

import Mathlib
import Definitions.Def_KaelblingPOMDP_Witness_Useful

namespace KaelblingPOMDP.Witness

open Finset

universe u

/-- §4.4, p. 114 (Kaelbling, Littman, Cassandra, *Planning and acting in partially observable stochastic domains*,
Artificial Intelligence 101:99–134 (1998)): the Q-function
`Q^a_t(b) = Σ_s b(s) R(s, a) + γ Σ_o Pr(o | a, b) V_{t−1}(SE(b, a, o))` (`t = n + 2`) is the value of
taking action `a` in belief state `b` and continuing optimally for `t − 1` steps, and "Since V is
the value of the best action, we have V_t(b) = max_a Q^a_t(b)". For every belief state `b`:

1. `Q^a_t(b)` is the maximum of `V_p(b)` over all t-step trees `p` with root action `a`;
2. `Q^a_t(b)` is the maximum of `V_p(b)` over the candidate set `C^a_t` (root `a`, every subtree in
   `V_{t−1}`), so one-step lookahead using `V_{t−1}` computes it;
3. `V_t(b) = max_a Q^a_t(b)`.

**Formalization Note** "Maximum" is stated with `IsGreatest` (the value is attained in the set);
in (1) and (2) this includes the nonemptiness of the set. `Qfun` multiplies the term of an
observation with `Pr(o | a, b) = 0` by zero. -/
theorem Q_function {S A Ω : Type u} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A] [DecidableEq A]
    [Nonempty A] [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (M : POMDP S A Ω) (hM : M.IsValid) (a : A) (n : ℕ) (b : S → ℝ) (hb : b ∈ stdSimplex ℝ S) :
    IsGreatest ((fun p : PolicyTree A Ω (n + 1) => valueAt M p b) '' {p | p.action = a})
        (Qfun M a n b) ∧
      IsGreatest ((fun p => valueAt M p b) '' (candidates M a n : Set (PolicyTree A Ω (n + 1))))
        (Qfun M a n b) ∧
      optValue M (n + 1) b = Finset.univ.sup' Finset.univ_nonempty (fun a' => Qfun M a' n b) := by sorry

end KaelblingPOMDP.Witness
