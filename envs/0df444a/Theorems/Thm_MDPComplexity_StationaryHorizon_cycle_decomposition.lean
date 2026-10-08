-- Prove2me | Theorems.Thm_MDPComplexity_StationaryHorizon_cycle_decomposition
-- name    : MDPComplexity.StationaryHorizon.cycle_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:45:01.543977+00:00
-- url     : https://prove2.me/theorems/0bf18e7f-761d-45bd-991d-92b15fdb5ce1
-- title:
--   A decision walk decomposes into a simple path and simple cycles
-- statement:
--   Let $W$ be an $l$-arc walk in a finite stationary deterministic process. There are a simple path $P$ and a finite list of simple cycles $C_1,\ldots,C_m$ such that $P$ has the same initial and final states as $W$, every cycle is based at a state visited by $W$, the cycles and path use exactly the multiset of decision arcs in $W$, and
--
--   $$l=|P|+\sum_{j=1}^{m}|C_j|,\qquad c(W)=c(P)+\sum_{j=1}^{m}c(C_j).$$
--
--   This records the length and cost preservation of the cycle removal described before Theorem 5.
--
--   **Formalization Note** The list records cycles with multiplicity. A loop is a simple cycle of one arc. The decomposition records the attachment state of each removed cycle. Equality of arc multisets distinguishes parallel decisions.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 447, §3 The finite horizon, stationary case, cycle-removal paragraph, https://doi.org/10.1287/moor.12.3.441

import Mathlib
import Definitions.Def_MDPComplexity_StationaryHorizon_Model

namespace MDPComplexity.StationaryHorizon

variable {S : Type} [Fintype S]

/-- §3, p. 447: repeatedly removing the first simple cycle leaves a simple path.
The recorded cycles preserve the original walk's arc count and cost. -/
theorem cycle_decomposition (M : DetMDP S) {l : ℕ} (W : M.Walk l) :
    ∃ (p : ℕ) (P : M.Walk p) (Cs : List (Σ k : ℕ, M.Walk k)),
      M.IsCycleDecomposition W P Cs := by sorry

end MDPComplexity.StationaryHorizon
