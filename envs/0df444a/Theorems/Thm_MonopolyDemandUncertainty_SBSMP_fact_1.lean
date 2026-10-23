-- Prove2me | Theorems.Thm_MonopolyDemandUncertainty_SBSMP_fact_1
-- name    : MonopolyDemandUncertainty.SBSMP.fact_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:11:24.048088+00:00
-- url     : https://prove2.me/theorems/90c8c0f7-ad6e-433a-93cc-965633bbe367
-- title:
--   Fact 1, p. 4 (PDF 5) — under BIC, every valuation that consumes only in state i pays the same price
-- statement:
--   Consider the two-state monopoly economy with the standing assumptions and Condition 1. Let $(x,t)$ be a deterministic mechanism satisfying BIC, and for $i \in \{1,2\}$ let $V_i$ be the set of valuations in $V$ that consume in state $i$ only. Then for all $v, \hat v \in V_i$,
--   $$t_i(v) = t_i(\hat v).$$
--
--   Fact 1 says that a BIC mechanism treats all types of $V_i$ as facing a single posted price in state $i$; it is the first step towards the interval structure of optimal mechanisms.
--
--   **Formalization Note** The positivity of the weights $\alpha_i(-D_i'(v))$, which the argument divides by, comes from Condition 1 and $0<\alpha_1<1$.
-- source:
--   Peck, Rampal, Optimal Monopoly Mechanisms with Demand Uncertainty, Mathematics of Operations Research (2021), Articles in Advance, doi:10.1287/moor.2020.1120, p. 4, Fact 1

import Mathlib
import Definitions.Def_MonopolyDemandUncertainty_SBSMP_Setting

namespace MonopolyDemandUncertainty.SBSMP

open MeasureTheory Set

/-- Fact 1, p. 4 (PDF 5): under BIC, all types in `V_i` (consuming in state `i` only) pay the
same price in state `i`. Index `0` is the paper's state 1, index `1` its state 2. -/
theorem fact_1 (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (M : Mechanism)
    (hBIC : E.IsBIC M) (i : Fin 2) :
    ∀ v ∈ E.onlySet M i, ∀ w ∈ E.onlySet M i, M.t i v = M.t i w := by sorry
end MonopolyDemandUncertainty.SBSMP
