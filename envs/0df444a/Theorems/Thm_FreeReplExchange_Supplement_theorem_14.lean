-- Prove2me | Theorems.Thm_FreeReplExchange_Supplement_theorem_14
-- name    : FreeReplExchange.Supplement.theorem_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:39:21.769282+00:00
-- url     : https://prove2.me/theorems/dad8b1ca-c74a-45a5-b2ac-b92e0f5e7028
-- title:
--   Theorem 14 -- HEC makes the initial allocation Pareto-efficient
-- statement:
--   Let an ESC coalition have aggregate competition $b_i=\sum_{j\ne i}\beta_{ij}\ge1$ for every agent. Then the initial allocation is Pareto-efficient in
--
--   $$
--   Y(x^{(0)})=\{y:y\ge x^{(0)}\},
--   $$
--
--   and hence is Pareto-efficient in the exchange-outcome class $X(x^{(0)},A)$.
--
--   Differences from the source:
--   - encoding: a nonempty finite set of agents with the paper's fixed order and finitely many goods → a nonempty finite linearly ordered type `A` and goods `Fin m`; reason: exact finite representation used by the published base mission, with nonemptiness made explicit because the source proof chooses a minimizing agent
--   - encoding: the classes Y and X → `dominatingAllocations` and `exchangeOutcomes`; reason: these are the source definitions with all agents participating
--   - generalization: every good is initially held by at least one agent as the paper's WLOG convention → no initial-coverage hypothesis; reason: the proof of Theorem 14 does not use coverage, and the Lean claim specializes to every source instance
-- source:
--   Yang--Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967...), Theorem 14, p.40 (PDF p.42), eq. (23)

import Mathlib
import Definitions.Def_FreeReplExchange_Supplement_IsExchangeProtocol

set_option autoImplicit false

namespace FreeReplExchange.Supplement

/-- Theorem 14, Yang--Kandasamy, *Pairwise Exchanges of Freely Replicable Goods with Negative
Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967...), p. 40 (PDF p. 42): in every
ESC high-externality coalition, the initial allocation is Pareto-efficient in the larger allocation
class `Y`, and hence in the exchange-outcome class `X`. -/
theorem theorem_14 {A : Type*} [Fintype A] [LinearOrder A] [Nonempty A] {m : ℕ}
    (x0 : A → Fin m → Bool) (U : A → A → Fin m → ℝ) (β : A → A → ℝ)
    (hESC : IsESC U β) (hHEC : IsHEC β) :
    ParetoEfficientIn U (dominatingAllocations x0) x0 ∧
      ParetoEfficientIn U (exchangeOutcomes x0 U Finset.univ) x0 := by sorry

end FreeReplExchange.Supplement
