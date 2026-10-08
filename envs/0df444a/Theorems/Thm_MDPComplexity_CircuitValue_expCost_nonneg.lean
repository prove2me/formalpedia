-- Prove2me | Theorems.Thm_MDPComplexity_CircuitValue_expCost_nonneg
-- name    : MDPComplexity.CircuitValue.expCost_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:53:13.945042+00:00
-- url     : https://prove2.me/theorems/74aeaa55-0c66-46ff-96f3-393515e9cf52
-- title:
--   Proof of Theorem 1 (p. 445): the expected cost of the circuit process cannot be less than zero
-- statement:
--   Let $C$ be a circuit with $k\ge1$ triples and let $M$ be the Markov decision process built from $C$ in the proof of Theorem 1 (initial state: the last triple $k$; horizon $k$). Then for every policy $\delta(s,t)$,
--   $$
--   J_k(\delta)=\mathbb E_\delta\Bigl[\sum_{t=0}^{k}c\bigl(s_t,\delta(s_t,t)\bigr)\Bigr]\ \ge\ 0 .
--   $$
--
--   This is the remark "(it cannot be less)" in the proof of Theorem 1: every cost of $M$ is $0$ or $1$, so the optimal expected cost is at most $0$ exactly when it equals $0$.
--
--   **Formalization Note** The expected cost is the sum over trajectories of the model definition, with the paper's §2 horizon convention $\sum_{t=0}^{T}$ and $T=k$.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 445, §3, proof of Theorem 1

import Mathlib
import Definitions.Def_MDPComplexity_CircuitValue_Model
import Definitions.Def_MDPComplexity_CircuitValue_Circuit
import Definitions.Def_MDPComplexity_CircuitValue_Reduction

namespace MDPComplexity.CircuitValue

theorem expCost_nonneg {k : ℕ} [NeZero k] (C : Circuit k) (δ : C.toMDP.Policy) :
    0 ≤ C.toMDP.expCost (some (Circuit.lastIdx k)) δ k := by sorry

end MDPComplexity.CircuitValue
