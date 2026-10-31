-- Prove2me | Theorems.Thm_MarkovEntanglementExact_local_transition_well_defined
-- name    : MarkovEntanglementExact.local_transition_well_defined
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:37.01671+00:00
-- url     : https://prove2.me/theorems/79ff49a4-5856-484a-8b27-c352286e37ca
-- title:
--   Eq. (2) and footnote 1, p.8 — the marginalized transition exists, is unique and is stochastic
-- statement:
--   Let $P$ be a transition matrix on $S_A\times S_B$ and $\mu$ a distribution with $\mu\ge0$, $\sum\mu=1$ and positive agent marginals. Then there is exactly one matrix $P_A$ satisfying Eq. (2), it is a transition matrix, and
--   $$P_A(a'\mid a)=\sum_{b'}\sum_b P\big((a',b')\mid(a,b)\big)\,\mu(b\mid a),\qquad \mu(b\mid a)=\frac{\mu(a,b)}{\mu(a)}.$$
--   The same holds for agent $B$.
--
--   This shows that the local transition matrices of the mission are well defined and that a statement quantified over them is about exactly one matrix for each agent.
--
--   **Formalization Note** `IsLocalTransitionA` is Eq. (2) multiplied through by the marginal. The display above ties it to the printed conditional form.
--
--   Differences from the source:
--   - generalization: P^π_AB of a two-agent MDP and policy → an arbitrary transition matrix P on a product of two finite sets; reason: the argument uses only the stochasticity of P; P^π_AB is an instance by M12
--   - generalization: μ is the stationary occupancy measure of a unichain, unique and strictly positive on states → μ is any distribution on joint pairs with μ ≥ 0, Σμ = 1 and positive agent marginals; reason: the derivation uses only the positivity of the conditioning marginals (footnote 1); the paper's occupancy measure is an instance, proved in the verification file OccupancyInstance
--   - encoding: Eq. (2) with the conditional μ(s_B, a_B | s_A, a_A) → IsLocalTransitionA/B, Eq. (2) multiplied through by the marginal; reason: equivalent under positive marginals; the quotient form is proved in M2
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Eq. (2) and footnote 1, p.8

import Mathlib
import Definitions.Def_markov_entanglement
import Definitions.Def_MarkovEntanglementExact_IsOccupancy

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact

/-- Eq. (2) is well defined: under the hypotheses of footnote 1 there is exactly one local
transition matrix for each agent, it is a transition matrix, and it is given by the printed
formula `P_A(a' | a) = Σ_{b'} Σ_b P_AB((a', b') | (a, b)) μ(b | a)`, with the conditional
`μ(b | a) = μ(a, b) / μ(a)`. The same holds for agent `B`.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Eq. (2) and
footnote 1, p.8.

**Formalization Note.** The published `IsLocalTransitionA` is Eq. (2) multiplied through by the
marginal. The last clause of each agent ties it to the printed quotient form. -/
theorem local_transition_well_defined
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    (P : Matrix (SA × SB) (SA × SB) ℝ) (hP : IsTransitionMatrix P)
    (μ : SA × SB → ℝ) (hμ : IsOccupancy μ) :
    (∃! PA : Matrix SA SA ℝ, IsLocalTransitionA P μ PA) ∧
      (∃! PB : Matrix SB SB ℝ, IsLocalTransitionB P μ PB) ∧
      (∀ PA : Matrix SA SA ℝ, IsLocalTransitionA P μ PA →
        IsTransitionMatrix PA ∧
          ∀ a a', PA a a' = ∑ b', ∑ b, P (a, b) (a', b') * (μ (a, b) / marginalA μ a)) ∧
      (∀ PB : Matrix SB SB ℝ, IsLocalTransitionB P μ PB →
        IsTransitionMatrix PB ∧
          ∀ b b', PB b b' = ∑ a', ∑ a, P (a, b) (a', b') * (μ (a, b) / marginalB μ b)) := by sorry

end MarkovEntanglementExact
