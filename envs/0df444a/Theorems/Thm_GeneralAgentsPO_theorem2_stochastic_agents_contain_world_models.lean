-- Prove2me | Theorems.Thm_GeneralAgentsPO_theorem2_stochastic_agents_contain_world_models
-- name    : GeneralAgentsPO.theorem2_stochastic_agents_contain_world_models
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:19:43.372582+00:00
-- url     : https://prove2.me/theorems/abe5b22d-9fa8-4571-8dc4-f27713995c69
-- title:
--   Theorem 2 (as proved): stochastic $\delta$-optimal agents contain world models
-- statement:
--   Let $\mathcal S,\mathcal A$ be finite sets with $|\mathcal A|\ge2$. Fix $s,s'\in\mathcal S$, $a\in\mathcal A$, an integer $n\ge1$ and $\delta<\tfrac12$, and put
--
--   $$L=\log\frac{2(1-\delta)}{1-2\delta}.$$
--
--   There is an estimator $\hat P$, a function of the goal-conditioned policy alone, with the following property. For every communicating cMDP $(\mathcal S,\mathcal A,P)$ and every goal-conditioned (possibly stochastic) policy $\pi$ that is $(2n+1)$-th-degree $\delta$-optimal for $P$,
--
--   $$\big|\hat P(\pi)-P(s'\mid s,a)\big|\le\sqrt{\frac{2P(s'\mid s,a)\big(1-P(s'\mid s,a)\big)}{n}L}+\frac{2L}{3n}+\frac1n.$$
--
--   In particular the error tends to $0$ at rate $O(1/\sqrt n)$. So a world model can be read off any sufficiently capable stochastic agent by querying it.
--
--   **Formalization Note** "An estimator defined by querying the policy" is a function of the policy that does not depend on $P$, chosen before $P$ and $\pi$. The proof uses only the first-step action probabilities of $\pi$ at a fixed state on the goals $\psi_{a,k}\vee\chi_{b,k}$, which is a special case. The hypotheses $|\mathcal A|\ge2$ and $n\ge1$ are not printed. The proof uses two distinct actions and divides by $n$, and with a single action the statement is false. The rate $O(1/\sqrt n)$ is a consequence of the bound and is not stated separately.
-- source:
--   Cifuentes, General Agents Contain World Models, even under Partial Observability and Stochasticity, arXiv:2602.03146v1 (2026), Section 4.1, Theorem 2, p. 8; proof pp. 8-10

import Mathlib
import Definitions.Def_GeneralAgentsPO_Basic

open GeneralAgentsWorldModels

namespace GeneralAgentsPO

theorem theorem2_stochastic_agents_contain_world_models {S A : Type*} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] (hA : 2 ≤ Fintype.card A) (s s' : S) (a : A) (n : ℕ) (hn : 1 ≤ n)
    (δ : ℝ) (hδ : δ < 1 / 2) :
    ∃ est : GCStochPolicy S S A → ℝ, ∀ M : CMP S A, M.IsCommunicating →
      ∀ π : GCStochPolicy S S A, IsDeltaOptimal M δ (PsiDepth (2 * n + 1)) π →
        |est π - M.P s a s'| ≤
          Real.sqrt (2 * M.P s a s' * (1 - M.P s a s') / n *
              Real.log (2 * (1 - δ) / (1 - 2 * δ))) +
            2 * Real.log (2 * (1 - δ) / (1 - 2 * δ)) / (3 * n) + 1 / n := by sorry

end GeneralAgentsPO
