-- Prove2me | Theorems.Thm_NogoodColoring1137_Main_task_equivalence
-- name    : NogoodColoring1137.Main.task_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T17:03:52.661467+00:00
-- url     : https://prove2.me/theorems/d4d41a09-98f8-432a-b71f-d30bd9bf349e
-- title:
--   Theorem 4 — All task reductions and oracle promises
-- statement:
--   On graphs of diameter at most two, with lists from three fixed colors, the complete chain is
--   $$\mathrm{Decision}\equiv_T^p\mathrm{ListDecision}\equiv_T^p\mathrm{Search}\equiv_T^p\mathrm{ListSearch}\le_T^p\mathrm{Counting}\equiv_T^p\mathrm{ListCounting}.$$
--   Each reduction has one finite oracle program, polynomially many calls and polynomial additional bit time. Every reached query graph has diameter at most two and at most the input's number of vertices. Search reductions work for every valid choice of oracle witness. Counts use binary fixed-name outputs, and search failure means no coloring exists.
--
--   This supplies all variants of the goal. **Formalization Note** Empty and singleton inputs are included. The promise applies at every reached query; counting-to-decision is not asserted.
--
--   Differences from the source:
--   - encoding: deterministic algorithms on explicit finite inputs → actual finite multitape bit-machine runs with binary integer and explicit output encodings; reason: the source fixes no bit layout; uniform programs and positive constants precede every input
-- source:
--   Philip Whittington, STOC 2027 submission #1137 (October 2026), Theorem 4, pp.21–23

import Definitions.Def_NogoodColoring1137_Main_Reductions

namespace NogoodColoring1137.Main

/-- Theorem 4, pp.21–23. Every Reduction includes the oracle size and diameter promises. -/
theorem task_equivalence :
    (Reduction 0 1 ∧ Reduction 1 0) ∧
    (Reduction 1 2 ∧ Reduction 2 1) ∧
    (Reduction 2 3 ∧ Reduction 3 2) ∧
    Reduction 3 4 ∧ (Reduction 4 5 ∧ Reduction 5 4) := by sorry

end NogoodColoring1137.Main
