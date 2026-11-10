-- Prove2me | Theorems.Thm_NogoodColoring1137_Main_main_theorem
-- name    : NogoodColoring1137.Main.main_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T17:02:32.957371+00:00
-- url     : https://prove2.me/theorems/a33e1974-8adb-460f-9cce-68e8c2a6ad16
-- title:
--   Theorem 1 — All six tasks and QP membership
-- statement:
--   Let $G$ be an $n$-vertex simple graph of diameter at most two and let $L(v)$ be arbitrary subsets of the fixed palette $\{0,1,2\}$. Six uniform finite deterministic programs, with positive global $A,C$ fixed before every input, compute ordinary/list decision, search and exact counting within
--   $$t\le A\exp(C[\ln(n+1)]^3).$$
--   Decision answers exactly whether a proper coloring exists. Search returns an actual proper coloring or reports failure exactly when none exists. Counting returns the exact binary count with color names distinguished. Both encoded decision languages, rejecting invalid strings and graphs outside the promise, belong to QP. Every graph size and list is included: the empty graph has one coloring and a one-vertex list count is its list size.
--
--   This is the full six-task cubic-logarithm target. **Formalization Note** Binary $n$, explicit adjacency and three list-membership bits give polynomial input length. Counts are at most $3^n$ and have $O(n+1)$ bits. Actual halting executions supply runtime; the small exhaustive branch is covered by the positive prefactor.
--
--   Differences from the source:
--   - generalization: graphs of diameter 2 → graphs of diameter at most 2, including complete and small graphs; reason: p.9 and all ingredients use at most two; §7 p.21 handles n=0,1; every source instance is included
--   - encoding: deterministic algorithms on explicit finite inputs → actual finite multitape bit-machine runs with binary integer and explicit output encodings; reason: the source fixes no bit layout; uniform programs and positive constants precede every input
-- source:
--   Philip Whittington, STOC 2027 submission #1137 (October 2026), Theorem 1, p.9 (also p.2)

import Definitions.Def_NogoodColoring1137_Main_Computation

namespace NogoodColoring1137.Main

/-- Theorem 1, p.9; diameter at most two is the explicitly declared generalization. -/
theorem main_theorem :
    (∃ (P : Fin 6 → IntMul.MultitapeTM) (A C : ℝ), 0 < A ∧ 0 < C ∧ SixTasks A C P) ∧
    InQP (DecisionLanguage false) ∧ InQP (DecisionLanguage true) := by sorry

end NogoodColoring1137.Main
