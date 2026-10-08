-- Prove2me | Theorems.Thm_KaelblingPOMDP_Witness_underestimate
-- name    : KaelblingPOMDP.Witness.underestimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:59.369283+00:00
-- url     : https://prove2.me/theorems/6d60ba24-96f1-4a95-87b9-168710f607c6
-- title:
--   §4.4.1, p. 115 — Q̂^a_t(b) ≤ Q^a_t(b): the approximation is always an underestimate
-- statement:
--   Let $\langle S, A, T, R, \Omega, O\rangle$ be a POMDP satisfying the standing hypotheses, $t \ge 2$ and $a$ an action. Let $U_a$ be a nonempty finite set of $t$-step trees with root action $a$ whose subtrees all lie in $\mathcal V_{t-1}$, and let $\hat Q^a_t(b) = \max_{p \in U_a} V_p(b)$. Then for every belief state $b$,
--   $$\hat Q^a_t(b) \le Q^a_t(b).$$
--
--   The witness algorithm grows $U_a$ from below; a belief state where the inequality is strict is a witness that $U_a$ is not yet complete.
--
--   **Formalization Note** $Q^a_t$ is `Qfun`, the formula of p. 114. Here $t = n + 2$.
-- source:
--   Kaelbling, Littman, Cassandra, Planning and acting in partially observable stochastic domains, Artificial Intelligence 101:99–134 (1998), DOI 10.1016/S0004-3702(98)00023-X, p. 115, §4.4.1

import Mathlib
import Definitions.Def_KaelblingPOMDP_Witness_Useful

namespace KaelblingPOMDP.Witness

open Finset

universe u

/-- §4.4.1, p. 115 (Kaelbling, Littman, Cassandra, *Planning and acting in partially observable stochastic domains*,
Artificial Intelligence 101:99–134 (1998)): "Note that for all b, Q̂^a_t(b) ⩽ Q^a_t(b); the approximation
is always an underestimate of the true value function." Here `U_a` is any nonempty set of candidate
trees (root `a`, subtrees in `V_{t−1}`), `Q̂^a_t(b) = max_{p ∈ U_a} V_p(b)`, and `t = n + 2`. -/
theorem underestimate {S A Ω : Type u} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A] [DecidableEq A]
    [Nonempty A] [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (M : POMDP S A Ω) (hM : M.IsValid) (a : A) (n : ℕ)
    (U : Finset (PolicyTree A Ω (n + 1))) (hU : U.Nonempty) (hUC : U ⊆ candidates M a n) :
    ∀ b ∈ stdSimplex ℝ S, upper M U hU b ≤ Qfun M a n b := by sorry

end KaelblingPOMDP.Witness
