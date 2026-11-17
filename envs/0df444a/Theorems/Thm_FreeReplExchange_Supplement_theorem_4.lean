-- Prove2me | Theorems.Thm_FreeReplExchange_Supplement_theorem_4
-- name    : FreeReplExchange.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:36:13.451604+00:00
-- url     : https://prove2.me/theorems/505b5349-db04-48c8-b1b8-f1bd709ce9b9
-- title:
--   Theorem 4 -- stability can force a Pareto-dominated outcome
-- statement:
--   There is an ESC instance with three agents and three goods whose initial allocation $x^{(0)}$ is not stable, but for which every stable allocation $x$ obtainable from $x^{(0)}$ through pairwise exchanges is Pareto-dominated by $x^{(0)}$:
--
--   $$
--   \neg\operatorname{Stable}(x^{(0)})
--   \quad\text{and}\quad
--   \forall x\in\mathcal R(x^{(0)}),\ \operatorname{Stable}(x)\Rightarrow x^{(0)}\succ_P x.
--   $$
--
--   The reachability class $\mathcal R(x^{(0)})$ contains finite executions of well-formed exchanges of initially owned goods; it is not the larger class $Y$.
--
--   Differences from the source:
--   - encoding: three agents and three goods → agents `Fin 3` and goods `Fin 3`; reason: finite index encoding with exactly the source cardinalities
--   - encoding: allocations obtainable through pairwise exchanges → `pairwiseExchangeOutcomes`, finite sets of well-formed initially-owned exchanges; reason: no onward sharing and Boolean union make sequential execution extensionally equal to execution of the finite set
-- source:
--   Yang--Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967...), Theorem 4, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_FreeReplExchange_Supplement_IsExchangeProtocol

set_option autoImplicit false

namespace FreeReplExchange.Supplement

/-- Theorem 4, Yang--Kandasamy, *Pairwise Exchanges of Freely Replicable Goods with Negative
Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967...), p. 23 (PDF p. 25): an ESC
instance with three agents and three goods has an unstable initial allocation, yet that initial
allocation Pareto-dominates every stable allocation obtainable from it through pairwise
exchanges. -/
theorem theorem_4 :
    ∃ (x0 : Fin 3 → Fin 3 → Bool) (U : Fin 3 → Fin 3 → Fin 3 → ℝ)
        (β : Fin 3 → Fin 3 → ℝ), IsESC U β ∧
      ¬ IsStableAllocation x0 U Finset.univ x0 ∧
      ∀ x ∈ pairwiseExchangeOutcomes x0 Finset.univ,
        IsStableAllocation x0 U Finset.univ x → ParetoDominates U x0 x := by sorry

end FreeReplExchange.Supplement
