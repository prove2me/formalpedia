-- Prove2me | Theorems.Thm_MDPComplexity_CircuitValue_exists_expCost_eq_zero
-- name    : MDPComplexity.CircuitValue.exists_expCost_eq_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:53:27.040153+00:00
-- url     : https://prove2.me/theorems/0fb2aa7d-3462-4611-8bfc-9ef86826e09d
-- title:
--   Proof of Theorem 1 (p. 445): if the circuit's value is true, some policy has expected cost zero
-- statement:
--   Let $C$ be a circuit with $k\ge1$ triples whose value is true, and let $M$ be the Markov decision process built from $C$ in the proof of Theorem 1, started at the last triple $k$ with horizon $k$. Then there is a policy $\delta(s,t)$ with
--   $$
--   \mathbb E_\delta\Bigl[\sum_{t=0}^{k}c\bigl(s_t,\delta(s_t,t)\bigr)\Bigr]=0 .
--   $$
--
--   This is the "if" half of the claim in the proof of Theorem 1: when the circuit is true one can choose, at each or gate, an input so that no false input is reachable.
--
--   **Formalization Note** The policy may be any time-dependent policy; the statement only asserts existence.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 445, §3, proof of Theorem 1

import Mathlib
import Definitions.Def_MDPComplexity_CircuitValue_Model
import Definitions.Def_MDPComplexity_CircuitValue_Circuit
import Definitions.Def_MDPComplexity_CircuitValue_Reduction

namespace MDPComplexity.CircuitValue

theorem exists_expCost_eq_zero {k : ℕ} [NeZero k] (C : Circuit k) (h : C.value = true) :
    ∃ δ : C.toMDP.Policy, C.toMDP.expCost (some (Circuit.lastIdx k)) δ k = 0 := by sorry

end MDPComplexity.CircuitValue
