-- Prove2me | Theorems.Thm_FreeReplExchange_Supplement_theorem_15
-- name    : FreeReplExchange.Supplement.theorem_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:39:50.743785+00:00
-- url     : https://prove2.me/theorems/752901e2-57d0-4bf3-b26d-3a28b00ad376
-- title:
--   Theorem 15 -- M3 is Pareto-efficient in X under LEC
-- statement:
--   Suppose an ESC coalition has aggregate competition $b_i=\sum_{j\ne i}\beta_{ij}<1$ for every agent. If every agent participates and follows the accepting policy, then M3's terminal allocation is Pareto-efficient in the exchange-outcome class $X(x^{(0)},A)$.
--
--   The conclusion is only relative to $X$, not the larger class $Y$; Pareto efficiency in $Y$ is the paper's Conjecture 1.
--
--   Differences from the source:
--   - encoding: a nonempty finite set of agents with the paper's fixed order and finitely many goods → a nonempty finite linearly ordered type `A` and goods `Fin m`; reason: exact finite representation used by the published base mission, with nonemptiness made explicit because the source proof chooses a minimizing agent
--   - encoding: all agents participate and accept → participating set `Finset.univ` and profile `acceptAll`; reason: exact Lean representation of the source conditions
--   - generalization: M3 with the paper's fixed global exchange order → M3 for every injective rank on exchanges; reason: the argument uses only that the global order is fixed and total, and every source order is such a rank
--   - generalization: every good is initially held by at least one agent as the paper's WLOG convention → no initial-coverage hypothesis; reason: the proof of Theorem 15 does not use coverage, and the Lean claim specializes to every source instance
-- source:
--   Yang--Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967...), Theorem 15, p.41 (PDF p.43)

import Mathlib
import Definitions.Def_FreeReplExchange_Supplement_IsExchangeProtocol

set_option autoImplicit false

namespace FreeReplExchange.Supplement

/-- Theorem 15, Yang--Kandasamy, *Pairwise Exchanges of Freely Replicable Goods with Negative
Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967...), p. 41 (PDF p. 43): under ESC
and low externality competition, when every agent participates and accepts, the allocation produced
by M3 is Pareto-efficient among the MIC exchange outcomes `X`.

**Formalization Note.** Participation is `Finset.univ` and the strategy profile is `acceptAll`.
The conclusion is only relative to `X`; no Pareto-efficiency claim is made for the larger class `Y`.
The injective rank is the published global tie order. -/
theorem theorem_15 {A : Type*} [Fintype A] [LinearOrder A] [Nonempty A] {m : ℕ}
    (x0 : A → Fin m → Bool) (U : A → A → Fin m → ℝ) (β : A → A → ℝ)
    (rk : Exchange A m → ℕ) (hrk : Function.Injective rk)
    (hESC : IsESC U β) (hLEC : IsLEC β) :
    ParetoEfficientIn U (exchangeOutcomes x0 U Finset.univ)
      (xInf x0 (M3 x0 U rk) Finset.univ acceptAll) := by sorry

end FreeReplExchange.Supplement
