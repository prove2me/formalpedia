-- Prove2me | Theorems.Thm_Freiman_lowerHistory_row2_exclusions_03
-- name    : Freiman.lowerHistory_row2_exclusions_03
-- status  : Proved
-- author  : @tp
-- created : 2026-09-14T09:01:16.096376+00:00
-- url     : https://prove2.me/theorems/3c14e909-6262-4267-b0db-a37ed2cbcb34
-- title:
--   Freiman H5 row-2 certificate exclusions, block 3
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

theorem Freiman.lowerHistory_row2_exclusions_03 : ∀ a ∈ ([(7,440,732),(1,440,769),(2,440,769),(4,440,769),(5,440,769),(6,440,769),(7,440,769),(1,440,795),(2,440,795),(4,440,795),(5,440,795),(6,440,795),(7,440,795),(1,440,814),(2,440,814),(4,440,814),(5,440,814),(6,440,814),(7,440,814),(1,440,833),(2,440,833),(4,440,833),(5,440,833),(6,440,833),(7,440,833),(1,440,836),(2,440,836),(4,440,836),(5,440,836),(1,440,893),(2,440,893),(4,440,893),(5,440,893),(1,440,896),(2,440,896),(4,440,896),(5,440,896),(1,440,901),(2,440,901),(4,440,901),(5,440,901),(6,440,904),(7,440,904),(6,440,1116),(7,440,1116),(6,440,1121),(7,440,1121),(1,440,1149),(2,440,1149),(4,440,1149)] : List (ℕ × ℕ × ℕ)), ∀ r s q : ℝ,
  certRectangleMem (lowerHistoryRectangles[a.1]?.getD ⟨0,1,0,1⟩) r s →
  ¬ (certBoundHolds (lowerHistoryBound a.2.1) r s q ∧
    certBoundHolds (lowerHistoryBound a.2.2) r s q) := by sorry
