-- Prove2me | Theorems.Thm_Freiman_lowerHistory_row2_exclusions_02
-- name    : Freiman.lowerHistory_row2_exclusions_02
-- status  : Proved
-- author  : @tp
-- created : 2026-09-14T09:01:29.424164+00:00
-- url     : https://prove2.me/theorems/a1ff5ddd-92eb-4c16-b75d-31a601e2540f
-- title:
--   Freiman H5 row-2 certificate exclusions, block 2
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

theorem Freiman.lowerHistory_row2_exclusions_02 : ∀ a ∈ ([(4,429,889),(5,429,889),(1,429,1149),(2,429,1149),(4,429,1149),(5,429,1149),(0,433,447),(3,433,447),(0,433,449),(3,433,449),(0,433,450),(3,433,450),(0,433,455),(3,433,455),(0,433,456),(3,433,456),(3,433,830),(0,433,839),(3,433,839),(1,436,836),(2,436,836),(4,436,836),(5,436,836),(1,436,884),(2,436,884),(4,436,884),(5,436,884),(1,436,895),(2,436,895),(4,436,895),(5,436,895),(6,436,1119),(7,436,1119),(1,440,665),(2,440,665),(4,440,665),(5,440,665),(6,440,665),(7,440,665),(1,440,711),(2,440,711),(4,440,711),(5,440,711),(6,440,711),(7,440,711),(1,440,732),(2,440,732),(4,440,732),(5,440,732),(6,440,732)] : List (ℕ × ℕ × ℕ)), ∀ r s q : ℝ,
  certRectangleMem (lowerHistoryRectangles[a.1]?.getD ⟨0,1,0,1⟩) r s →
  ¬ (certBoundHolds (lowerHistoryBound a.2.1) r s q ∧
    certBoundHolds (lowerHistoryBound a.2.2) r s q) := by sorry
