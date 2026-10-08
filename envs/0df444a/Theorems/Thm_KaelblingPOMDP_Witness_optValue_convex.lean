-- Prove2me | Theorems.Thm_KaelblingPOMDP_Witness_optValue_convex
-- name    : KaelblingPOMDP.Witness.optValue_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:46.269981+00:00
-- url     : https://prove2.me/theorems/89574b9d-be56-403d-9e02-0324fb593179
-- title:
--   §4.1, p. 110 — V_t(b) = max_{p∈P} b · α_p is convex on the belief simplex
-- statement:
--   Let $\langle S, A, T, R, \Omega, O\rangle$ be a POMDP satisfying the standing hypotheses and $t \ge 1$. Let $P$ be the finite set of all $t$-step policy trees and
--   $$V_t(b) = \max_{p \in P} b \cdot \alpha_p .$$
--   Then $V_t$ is a convex function on the set $B$ of belief states.
--
--   Each tree contributes a function $b \mapsto b \cdot \alpha_p$ that is linear in $b$, and $V_t$ is their upper surface; the paper concludes that $V_t$ is piecewise linear and convex. This geometric fact is what makes it possible to represent value functions by finite sets of vectors.
--
--   **Formalization Note** `optValue M n` is $V_{n+1}$. Piecewise linearity holds by definition (a maximum of finitely many linear functions); the theorem states convexity on `stdSimplex ℝ S`.
-- source:
--   Kaelbling, Littman, Cassandra, Planning and acting in partially observable stochastic domains, Artificial Intelligence 101:99–134 (1998), DOI 10.1016/S0004-3702(98)00023-X, p. 110, §4.1

import Mathlib
import Definitions.Def_KaelblingPOMDP_Witness_Useful

namespace KaelblingPOMDP.Witness

open Finset

universe u

/-- §4.1, p. 110 (Kaelbling, Littman, Cassandra, *Planning and acting in partially observable stochastic domains*,
Artificial Intelligence 101:99–134 (1998)): the optimal t-step value function
`V_t(b) = max_{p ∈ P} b · α_p` (`P` the finite set of all t-step policy trees) is the upper surface of
the linear functions `b ↦ b · α_p`, "So, V_t is piecewise-linear and convex": it is convex on the
belief simplex.

**Formalization Note** `optValue M n` is the maximum over all (n + 1)-step trees, so this is the
statement for `t = n + 1 ≥ 1`. Piecewise linearity is the definition (a maximum of finitely many
linear functions); the theorem asserts convexity. -/
theorem optValue_convex {S A Ω : Type u} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A] [DecidableEq A]
    [Nonempty A] [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (M : POMDP S A Ω) (hM : M.IsValid) (n : ℕ) :
    ConvexOn ℝ (stdSimplex ℝ S) (optValue M n) := by sorry

end KaelblingPOMDP.Witness
