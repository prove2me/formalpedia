-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_budget_energy
-- name    : NearlyOptimalPPR.Computation.recursive_budget_energy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T10:55:49.93573+00:00
-- url     : https://prove2.me/theorems/b720a2ba-c9ef-4ce1-8d58-516031d8ef40
-- title:
--   Recursive PageRank budget-energy invariant
-- statement:
--   For every finite reachable prefix of Algorithms 6–9, each open call whose episode budget is open has clipped residual energy bounded by the sum of its episode budget and the charges received during that episode. In the source's notation, the resulting mass bound is
--
--   $$\mu_j\le E_j\le Q_j+W_j.$$
--
--   Here $\mu_j$ is the active residual mass, $Q_j$ the episode's initial budget, and $W_j$ the accumulated incoming and activation charges. The virtual residual also accounts for earlier inactive layers. The assertion applies to every finite prefix, including a completed update that crosses the budget; it assumes neither termination nor an unexhausted current budget.
--
--   This invariant supplies the mass control used in Lemma 5.3 and the running-time analysis of Lemma 4.4.
--
--   **Formalization Note** The statement preserves the rowwise clipped-energy predicate; the displayed active-mass inequality is its downstream consequence. The graph has a nonisolated seed and the teleportation and root threshold are positive, with teleportation below one.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Lemma 5.3 and its proof pp.23–25; Algorithms 6–9; Lemma 4.4 p.18.

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
open NearlyOptimalPPR.Computation

theorem NearlyOptimalPPR.Computation.recursive_budget_energy (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    BudgetEnergyInvariant g s α (recursiveRun m g s α q ℓ schedule t) := by sorry
