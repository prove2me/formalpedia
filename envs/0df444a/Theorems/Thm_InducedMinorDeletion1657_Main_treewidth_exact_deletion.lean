-- Prove2me | Theorems.Thm_InducedMinorDeletion1657_Main_treewidth_exact_deletion
-- name    : InducedMinorDeletion1657.Main.treewidth_exact_deletion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:35:48.42994+00:00
-- url     : https://prove2.me/theorems/3ac007b8-beb1-46ad-8222-52c5d86ba7cd
-- title:
--   Corollary 5.2 — exact deletion parameterized by treewidth
-- statement:
--   For each fixed positive $t$ and arbitrary closed MSO sentence $\varphi$, one algorithm on every finite input graph $G$ outputs a minimum feasible deletion set, or a distinct failure output exactly when no feasible set exists. With $w=\operatorname{tw}(G)$, its running time is
--   $$C2^{C(w+1)\log_2(w+2)}(n+1)^c.$$
--   The constants depend only on $t,\varphi$. The graph alone is supplied: no decomposition, optimum, excluded minor, or hereditary formula is assumed. Exact optimality is comparison with all feasible subsets.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → graphs on Fin n, including n = 0; nonnegative treewidth from actual decompositions; reason: finite relabeling preserves every instance; empty treewidth zero changes no nonnegative-width predicate
--   - encoding: an algorithm and its running time → one finite multi-stack Turing machine with fixed input and distinct failure/subset output encodings; reason: actual halting steps, including output; polynomial simulation overhead is absorbed by the uniform constants
--   - reading: unqualified graph MSO formula → closed ordinary incidence MSO2 with no free constants and one trivial color; reason: the stronger standard MSO reading includes MSO1 and adds no hereditary, union-closure or satisfiability assumption
--   - encoding: w^{O(w)}n^{O(1)} and minimum output → the proof’s all-width bound and explicit infeasibility output; reason: handles small widths and unsatisfiable sentences without an invented minimum of an empty table
-- source:
--   Daniel Lokshtanov, Fahad Panolan, Saket Saurabh, Jie Xue, Meirav Zehavi, STOC 2027 submission #1657 (October 2026), p. 28 (PDF p. 29), Corollary 5.2

import Definitions.Def_InducedMinorDeletion1657_Main_Collections

set_option autoImplicit false
open Classical

namespace InducedMinorDeletion1657.Main

/-- Corollary 5.2, printed p. 28 / PDF p. 29. See the local source audit for conventions. -/
theorem treewidth_exact_deletion :
∀ (t : ℕ) (φ : Sentence), 0 < t →
  ∃ (P : Machine) (C c : ℕ), 0 < C ∧ 0 < c ∧
    ∀ G : InputGraph, ∃ o : Option (Finset (Fin G.n)),
      exactResult G t φ o ∧ machineOutputs P (graphTape G) (answerTape o)
        (widthTime C c G.n (width G.graph)) := by sorry

end InducedMinorDeletion1657.Main
