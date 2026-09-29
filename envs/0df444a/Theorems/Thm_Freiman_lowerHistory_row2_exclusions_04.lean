-- Prove2me | Theorems.Thm_Freiman_lowerHistory_row2_exclusions_04
-- name    : Freiman.lowerHistory_row2_exclusions_04
-- status  : Proved
-- author  : @tp
-- created : 2026-09-14T09:02:12.081707+00:00
-- url     : https://prove2.me/theorems/191af469-d57b-4d5c-b9e6-dc003d828e3e
-- title:
--   Freiman H5 row-2 certificate exclusions, block 4
-- statement:
--   Let $B_i(r,s,q)$ denote the original indexed history bound and let $R_j$ denote the original indexed rational rectangle. For each displayed triple $(j,\ell,u)$, the two bounds cannot hold simultaneously at any point of the rectangle. Thus
--
--   $$\forall(r,s)\in R_j\quad\forall q\in\mathbb R,\qquad\neg(B_\ell(r,s,q)\wedge B_u(r,s,q)).$$
--
--   The formal statement lists the complete triples. These exclusions are precisely the original witness inequalities used to resolve the necessary row-2 source alternatives and endpoint residuals in the H5 exception-anchor argument.
-- source:
--   Original Freiman lowerHistory witness catalogue and exact bound and rectangle indices. Prerequisite of https://prove2.me/theorem/bb9829c2-d91f-4bc0-a11c-3a75193cc00d .

import Definitions.Def_Freiman_lowerHistoryShared
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem Freiman.lowerHistory_row2_exclusions_04 : ∀ a ∈ ([(5,440,1149),(6,440,1149),(7,440,1149),(1,440,1153),(2,440,1153),(4,440,1153),(5,440,1153),(6,440,1153),(7,440,1153),(1,442,817),(2,442,817),(4,442,817),(5,442,817),(6,442,817),(7,442,817)] : List (ℕ × ℕ × ℕ)), ∀ r s q : ℝ,
  certRectangleMem (lowerHistoryRectangles[a.1]?.getD ⟨0,1,0,1⟩) r s →
  ¬ (certBoundHolds (lowerHistoryBound a.2.1) r s q ∧
    certBoundHolds (lowerHistoryBound a.2.2) r s q) := by sorry
