-- Prove2me | Theorems.Thm_MDPComplexity_CircuitValue_theorem1_reduction
-- name    : MDPComplexity.CircuitValue.theorem1_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:53:29.697809+00:00
-- url     : https://prove2.me/theorems/d46d3253-87cc-4ac7-8194-4b80b60bfd99
-- title:
--   Proof of Theorem 1 (p. 445): the circuit process has optimal expected cost ≤ 0 iff the circuit is true
-- statement:
--   Let $C=((a_i,b_i,c_i),\ i=1,\dots,k)$ be a circuit with $k\ge1$ triples, and let $M$ be the stationary Markov decision process built from $C$ in the proof of Theorem 1 of Papadimitriou–Tsitsiklis: one state per triple plus an absorbing state $q$, cost $1$ at false inputs and $0$ elsewhere, a free choice between $b_i$ and $c_i$ at or gates, and a fair random move to $b_i$ or $c_i$ at and gates. Start $M$ at the last triple $k$ and use the horizon $k$. Then
--   $$
--   \inf_{\delta}\ \mathbb E_\delta\Bigl[\sum_{t=0}^{k}c\bigl(s_t,\delta(s_t,t)\bigr)\Bigr]\ \le\ 0
--   \quad\Longleftrightarrow\quad \text{the value of } C \text{ is true},
--   $$
--   where the infimum is over all policies $\delta(s,t)$.
--
--   This is the correctness of the reduction from the circuit value problem to the finite-horizon Markov decision problem, the mathematical content of the P-hardness half of Theorem 1 ("The Markov Decision Process problem is P-complete …").
--
--   **Formalization Note** Only the correctness of the reduction is stated: membership in P, the log-space computability of the construction and P-completeness itself are not formalized. The optimum is a real infimum over all time-dependent policies, never over stationary ones only. The horizon convention is the §2 sum $\sum_{t=0}^{T}$ with $T=k$ (every trajectory reaches an input by time $k-1$ and then $q$ by time $k$, so the convention does not change the claim). Triple $k$ need not be a gate.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 444, Theorem 1; p. 445, §3, proof of Theorem 1

import Mathlib
import Definitions.Def_MDPComplexity_CircuitValue_Model
import Definitions.Def_MDPComplexity_CircuitValue_Circuit
import Definitions.Def_MDPComplexity_CircuitValue_Reduction

namespace MDPComplexity.CircuitValue

theorem theorem1_reduction {k : ℕ} [NeZero k] (C : Circuit k) :
    C.toMDP.optCost (some (Circuit.lastIdx k)) k ≤ 0 ↔ C.value = true := by sorry

end MDPComplexity.CircuitValue
