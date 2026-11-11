-- Prove2me | Theorems.Thm_InducedMinorDeletion1657_Main_subexponential_deletion
-- name    : InducedMinorDeletion1657.Main.subexponential_deletion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:35:34.878866+00:00
-- url     : https://prove2.me/theorems/65ef5a7b-68cc-488a-ae89-a2bc874d38e7
-- title:
--   Theorem 1.1 — subexponential exact MSO vertex deletion
-- statement:
--   For every fixed finite graph $H$, nonnegative integer $t$ and arbitrary closed graph MSO sentence $\varphi$, there is one exact optimizer for all $H$-induced-minor-free input graphs. A set $S$ is feasible precisely when $\operatorname{tw}(G-S)\le t$ and $G-S\models\varphi$. On feasible inputs the optimizer returns a minimum such set, whose cardinality is the true optimum $k$, within
--   $$C2^{C(k+1)^{2/3}\log_2(k+2)}(n+1)^c.$$
--   There is also one budget algorithm, correct for every nonnegative budget $b$, returning a feasible set of size at most $b$ exactly when one exists, within the same bound with $b$ in place of $k$. Failure is a distinct output. On infeasible inputs the optimizer reports failure within the budget bound at $b=n$; no finite optimum is assigned. Both programs and constants are chosen before every graph and budget. The optimizer is given only the graph, not $k$, a representation, a modulator or a decomposition. This is exact minimization for every sentence, with no hereditary or disjoint-union assumption.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → graphs on Fin n, including n = 0; nonnegative treewidth from actual decompositions; reason: finite relabeling preserves every instance; empty treewidth zero changes no nonnegative-width predicate
--   - encoding: an algorithm and its running time → one finite multi-stack Turing machine with fixed input and distinct failure/subset output encodings; reason: actual halting steps, including output; polynomial simulation overhead is absorbed by the uniform constants
--   - reading: unqualified graph MSO formula → closed ordinary incidence MSO2 with no free constants and one trivial color; reason: the stronger standard MSO reading includes MSO1 and adds no hereditary, union-closure or satisfiability assumption
--   - generalization: positive t in the numbered theorem (Section 3 uses N={1,2,…}) → every nonnegative t, as in the abstract; reason: at t=0 apply the positive-t theorem with t′=1 and φ conjoined with edgelessness; feasible sets and optima are identical
--   - encoding: 2^{Õ(k^{2/3})}n^{O(1)} with k the optimum → uniform C2^{C(k+1)^{2/3}log₂(k+2)}(n+1)^c, plus an all-budget algorithm and explicit failure; reason: Sections 4–6 support one logarithm; increasing budgets through first success gives exact optimization, b=n certifies infeasibility, and small parameters are saturated
-- source:
--   Daniel Lokshtanov, Fahad Panolan, Saket Saurabh, Jie Xue, Meirav Zehavi, STOC 2027 submission #1657 (October 2026), p. 3 (PDF p. 4), Theorem 1.1

import Definitions.Def_InducedMinorDeletion1657_Main_Collections

set_option autoImplicit false
open Classical

namespace InducedMinorDeletion1657.Main

/-- Theorem 1.1, printed p. 3 / PDF p. 4. See the local source audit for conventions. -/
theorem subexponential_deletion :
∀ (H : InputGraph) (t : ℕ) (φ : Sentence),
  ∃ (Budget Optimize : Machine) (C c : ℕ), 0 < C ∧ 0 < c ∧
    (∀ (G : InputGraph) (b : ℕ), excluded H.graph G.graph →
      ∃ o : Option (Finset (Fin G.n)), budgetResult G t φ b o ∧
        machineOutputs Budget (budgetTape G b) (answerTape o) (mainTime C c G.n b)) ∧
    (∀ G : InputGraph, excluded H.graph G.graph →
      ∃ o : Option (Finset (Fin G.n)), exactResult G t φ o ∧
        machineOutputs Optimize (graphTape G) (answerTape o)
          (mainTime C c G.n (resultParameter o))) := by sorry

end InducedMinorDeletion1657.Main
