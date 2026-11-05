-- Prove2me | Theorems.Thm_HadwigerConj_complete_graph_case
-- name    : HadwigerConj.complete_graph_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:19:35.830661+00:00
-- url     : https://prove2.me/theorems/0589afad-00b1-4eea-a929-66bbb89cfa98
-- title:
--   Hadwiger conjecture: Complete input graphs
-- statement:
--   For every n and t, the complete graph on n vertices is t-colorable if it has no complete minor of order t+1.
-- source:
--   Elementary special case / supporting lemma for Challenge 01. Definitions: https://tenchallenges.github.io/ten-challenges/#problems

import Definitions.Def_HadwigerConj_Defs
open SimpleGraph HadwigerConj

theorem HadwigerConj.complete_graph_case (n t : ℕ)
    (h : ¬ HasCompleteMinor (completeGraph (Fin n)) (t + 1)) :
    (completeGraph (Fin n)).Colorable t := by sorry
