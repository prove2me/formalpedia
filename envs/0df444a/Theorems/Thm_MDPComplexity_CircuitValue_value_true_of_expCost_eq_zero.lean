-- Prove2me | Theorems.Thm_MDPComplexity_CircuitValue_value_true_of_expCost_eq_zero
-- name    : MDPComplexity.CircuitValue.value_true_of_expCost_eq_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:53:21.691331+00:00
-- url     : https://prove2.me/theorems/90dd7adc-59f4-44b2-a2f7-55da15c2e843
-- title:
--   Proof of Theorem 1 (p. 445): if some policy has expected cost zero, the circuit's value is true
-- statement:
--   Let $C$ be a circuit with $k\ge1$ triples and $M$ the Markov decision process built from $C$ in the proof of Theorem 1, started at the last triple $k$ with horizon $k$. If a policy $\delta(s,t)$ has expected cost
--   $$
--   \mathbb E_\delta\Bigl[\sum_{t=0}^{k}c\bigl(s_t,\delta(s_t,t)\bigr)\Bigr]=0,
--   $$
--   then the value of $C$ is true.
--
--   This is the "only if" half of the claim in the proof of Theorem 1: the false inputs, the only states with positive cost, are unreachable, so the decisions of $\delta$ choose, at each or gate, an input of true value.
--
--   **Formalization Note** $\delta$ ranges over all time-dependent policies, not only stationary ones. The horizon convention is the §2 sum $\sum_{t=0}^{T}$ with $T=k$.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 445, §3, proof of Theorem 1

import Mathlib
import Definitions.Def_MDPComplexity_CircuitValue_Model
import Definitions.Def_MDPComplexity_CircuitValue_Circuit
import Definitions.Def_MDPComplexity_CircuitValue_Reduction

namespace MDPComplexity.CircuitValue

theorem value_true_of_expCost_eq_zero {k : ℕ} [NeZero k] (C : Circuit k)
    (δ : C.toMDP.Policy) (h : C.toMDP.expCost (some (Circuit.lastIdx k)) δ k = 0) :
    C.value = true := by sorry

end MDPComplexity.CircuitValue
