-- Prove2me | Theorems.Thm_InducedMinorDeletion1657_Main_complete_deletion_table
-- name    : InducedMinorDeletion1657.Main.complete_deletion_table
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:35:40.455187+00:00
-- url     : https://prove2.me/theorems/d51bd3b7-80a0-4c10-973a-c9ca3367bff3
-- title:
--   Lemma 5.1 — complete MSO deletion table
-- statement:
--   Fix a positive treewidth bound $t$ and an arbitrary closed MSO sentence $\varphi$. One algorithm computes, on every finite graph $G$ of treewidth $w$, a complete $(t,\varphi)$-table in time
--   $$C2^{C(w+1)\log_2(w+2)}(n+1)^c.$$
--   Every table entry is a feasible deletion set. For every feasible $R$, the table contains $S$ with $|S|\le|R|$ and $G-S$ of the same $\varphi$-type as $G-R$ under all finite empty-boundary extensions. Thus the empty table is valid exactly when there is no feasible deletion. No decomposition is part of the input. This retains both table clauses for nonhereditary as well as hereditary formulas.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → graphs on Fin n, including n = 0; nonnegative treewidth from actual decompositions; reason: finite relabeling preserves every instance; empty treewidth zero changes no nonnegative-width predicate
--   - encoding: an algorithm and its running time → one finite multi-stack Turing machine with fixed input and distinct failure/subset output encodings; reason: actual halting steps, including output; polynomial simulation overhead is absorbed by the uniform constants
--   - reading: unqualified graph MSO formula → closed ordinary incidence MSO2 with no free constants and one trivial color; reason: the stronger standard MSO reading includes MSO1 and adds no hereditary, union-closure or satisfiability assumption
--   - encoding: w^{O(w)}n^{O(1)} → C2^{C(w+1)log₂(w+2)}(n+1)^c; reason: this is the explicit all-width bound in the proof on printed p.28, including w=0 and w=1
-- source:
--   Daniel Lokshtanov, Fahad Panolan, Saket Saurabh, Jie Xue, Meirav Zehavi, STOC 2027 submission #1657 (October 2026), p. 25 (PDF p. 26), Lemma 5.1

import Definitions.Def_InducedMinorDeletion1657_Main_Collections

set_option autoImplicit false
open Classical

namespace InducedMinorDeletion1657.Main

/-- Lemma 5.1, printed p. 25 / PDF p. 26. See the local source audit for conventions. -/
theorem complete_deletion_table :
∀ (t : ℕ) (φ : Sentence), 0 < t →
  ∃ (P : Machine) (C c : ℕ), 0 < C ∧ 0 < c ∧
    ∀ G : InputGraph, ∃ L : List (Finset (Fin G.n)),
      deletionTable G.graph t φ L ∧
      machineOutputs P (graphTape G) (tableTape L)
        (widthTime C c G.n (width G.graph)) := by sorry

end InducedMinorDeletion1657.Main
