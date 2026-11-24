-- Prove2me | Theorems.Thm_GeneralAgentsPO_theorem4_width_two_optimal
-- name    : GeneralAgentsPO.theorem4_width_two_optimal
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:21:31.459646+00:00
-- url     : https://prove2.me/theorems/99ec65ef-096c-46a1-b2ce-07c1a5c570c1
-- title:
--   Theorem 4, first claim (as proved): optimal deterministic agents on width-2 goals recover transitions with error $O(\log n/n)$
-- statement:
--   Let $\mathcal S,\mathcal A$ be finite sets with $|\mathcal A|\ge2$, and fix $s,s'\in\mathcal S$ and $a\in\mathcal A$. Then there are constants $C$ and $N$ with the following property. For every $n\ge N$ there is an estimator $\hat P_n$, a function of the goal-conditioned policy alone, such that for every communicating cMDP $(\mathcal S,\mathcal A,P)$ and every deterministic goal-conditioned policy $\pi$ that is optimal on $\Psi_{2n+1,2}$ (the goals of depth $2n+1$ and width $2$),
--
--   $$\big|\hat P_n(\pi)-P(s'\mid s,a)\big|\le C\,\frac{\log n}{n}.$$
--
--   So optimality on a set of goals far smaller than $\Psi_{2n+1}$ already determines the world model, at a faster rate than Theorem 1.
--
--   **Formalization Note** "Error scaling as $O(\log n/n)$" is written with explicit constants $C,N$ that may depend on $\mathcal S,\mathcal A,s,s',a$ but not on $P$, $\pi$ or $n$. "Optimal" is $0$-optimal. The hypothesis $|\mathcal A|\ge2$ is added: with a single action every policy is optimal and carries no information. $\Psi_{2n+1,2}$ contains only goals of depth exactly $2n+1$. Some goals queried in the paper's proof, such as $\xi_{1,1}$, have smaller depth. The fix is routine: prepending $\top[\mathcal S\times\mathcal A]$ to a sequential goal raises its depth without changing its meaning or width, and $\xi_{n,n}$ can replace $\xi_{1,1}$ in the test $p\le\frac12$.
-- source:
--   Cifuentes, General Agents Contain World Models, even under Partial Observability and Stochasticity, arXiv:2602.03146v1 (2026), Section 4.3, Theorem 4, p. 15; proof pp. 15-16

import Mathlib
import Definitions.Def_GeneralAgentsPO_Basic

open GeneralAgentsWorldModels

namespace GeneralAgentsPO

theorem theorem4_width_two_optimal {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] (hA : 2 ≤ Fintype.card A) (s s' : S) (a : A) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∃ est : GCStochPolicy S S A → ℝ, ∀ M : CMP S A, M.IsCommunicating →
      ∀ π : GCStochPolicy S S A, (∀ ψ, (π ψ).IsDeterministic) →
        IsDeltaOptimal M 0 (PsiDepthWidth (2 * n + 1) 2) π →
          |est π - M.P s a s'| ≤ C * Real.log n / n := by sorry

end GeneralAgentsPO
