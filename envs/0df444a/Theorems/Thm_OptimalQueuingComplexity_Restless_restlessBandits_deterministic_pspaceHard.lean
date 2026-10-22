-- Prove2me | Theorems.Thm_OptimalQueuingComplexity_Restless_restlessBandits_deterministic_pspaceHard
-- name    : OptimalQueuingComplexity.Restless.restlessBandits_deterministic_pspaceHard
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T12:49:27.813654+00:00
-- url     : https://prove2.me/theorems/f5228405-1674-4a24-ba7a-a5d46fd58bc6
-- title:
--   Theorem 4 — RESTLESS BANDITS with deterministic transition rules is PSPACE-hard
-- statement:
--   In the RESTLESS BANDITS problem with deterministic transition rules we are given $n \ge 1$ bandits on a common finite state space $S = \{1,\dots,M\}$, their initial states, a rule $P : S \to S$ applied to the bandit that is played and a rule $Q : S \to S$ applied to every bandit that is not played, rational costs $c, d$ on $S$, and a rational threshold $K$. A policy $\pi : S^n \to \{1,\dots,n\}$ chooses the bandit $i(t) = \pi(X_1(t),\dots,X_n(t))$ to play; the cost at time $t$ is $C(t) = c(X_{i(t)}(t)) + \sum_{i\ne i(t)} d(X_i(t))$. The question is whether some policy has
--   $$\limsup_{T\to\infty} \frac{1}{T}\sum_{t=1}^{T} C(t) \;\le\; K .$$
--
--   **Theorem 4.** This problem is PSPACE-hard: every language decidable in polynomial space reduces to it by a polynomial-time many-one reduction.
--
--   The classical multi-armed bandit ($Q = \mathrm{id}$, $d = 0$) is solved in polynomial time by Gittins indices. Theorem 4 says that no such efficient procedure is to be expected for restless bandits, even when all transitions are deterministic, unless P = PSPACE.
--
--   **Formalization Note.** The paper defines only the optimization problem; the decision version "average cost at most $K$" is this formalization's convention, and the paper's reduction uses it with $K = 0$. The theorem states hardness, as Theorem 4 does. The last sentence of the paper's proof says "thus proving PSPACE-completeness" and the introduction calls the problem PSPACE-complete, but membership in PSPACE is not argued in the paper and is not part of this statement.
-- source:
--   Papadimitriou & Tsitsiklis, The Complexity of Optimal Queuing Network Control, Math. Oper. Res. 24(2) (1999), p. 303, Theorem 4

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete
import Definitions.Def_OptimalQueuingComplexity_Restless_restlessBandits

namespace OptimalQueuingComplexity.Restless

/-- Papadimitriou & Tsitsiklis 1999, p. 303, Theorem 4: RESTLESS BANDITS with deterministic
transition rules is PSPACE-hard. -/
theorem restlessBandits_deterministic_pspaceHard :
    PSPACEHard Instance.enc restlessBandits := by sorry

end OptimalQueuingComplexity.Restless
