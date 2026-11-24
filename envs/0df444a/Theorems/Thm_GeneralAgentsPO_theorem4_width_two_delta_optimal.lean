-- Prove2me | Theorems.Thm_GeneralAgentsPO_theorem4_width_two_delta_optimal
-- name    : GeneralAgentsPO.theorem4_width_two_delta_optimal
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:22:14.069547+00:00
-- url     : https://prove2.me/theorems/d36290d0-bc04-4b53-bd7d-e097cc910737
-- title:
--   Theorem 4, second claim (as proved): $\delta$-optimal deterministic agents on width-2 goals recover transitions with error $O(\log n/n)$
-- statement:
--   Let $\mathcal S,\mathcal A$ be finite sets with $|\mathcal A|\ge2$, fix $s,s'\in\mathcal S$, $a\in\mathcal A$ and $\delta<\tfrac12$. Then there are constants $C$ and $N$ with the following property. For every $n\ge N$ there is an estimator $\hat P_n$, a function of the goal-conditioned policy alone, such that for every communicating cMDP $(\mathcal S,\mathcal A,P)$ and every deterministic goal-conditioned policy $\pi$ that is $\delta$-optimal on $\Psi_{6n+1,2}$,
--
--   $$\big|\hat P_n(\pi)-P(s'\mid s,a)\big|\le C\,\frac{\log n}{n}.$$
--
--   **Formalization Note** The constants $C,N$ may depend on $\delta$ and on $\mathcal S,\mathcal A,s,s',a$, but not on $P$, $\pi$ or $n$. The hypothesis $|\mathcal A|\ge2$ is added as in the first claim. The goals $\xi_{r,n}$ with $r<3n$ used in the proof have depth less than $6n+1$ and are not in $\Psi_{6n+1,2}$ as defined. The fix is routine: prepending $\top[\mathcal S\times\mathcal A]$ to each sequential goal raises its depth to $6n+1$ without changing its meaning or width.
-- source:
--   Cifuentes, General Agents Contain World Models, even under Partial Observability and Stochasticity, arXiv:2602.03146v1 (2026), Section 4.3, Theorem 4, p. 15; proof pp. 16-17, eq. (6)

import Mathlib
import Definitions.Def_GeneralAgentsPO_Basic

open GeneralAgentsWorldModels

namespace GeneralAgentsPO

theorem theorem4_width_two_delta_optimal {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] (hA : 2 ≤ Fintype.card A) (s s' : S) (a : A) (δ : ℝ) (hδ : δ < 1 / 2) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∃ est : GCStochPolicy S S A → ℝ, ∀ M : CMP S A, M.IsCommunicating →
      ∀ π : GCStochPolicy S S A, (∀ ψ, (π ψ).IsDeterministic) →
        IsDeltaOptimal M δ (PsiDepthWidth (6 * n + 1) 2) π →
          |est π - M.P s a s'| ≤ C * Real.log n / n := by sorry

end GeneralAgentsPO
