-- Prove2me | Theorems.Thm_Freiman_lowerHistory_row2_exclusions_01
-- name    : Freiman.lowerHistory_row2_exclusions_01
-- status  : Proved
-- author  : @tp
-- created : 2026-09-14T09:01:25.820695+00:00
-- url     : https://prove2.me/theorems/c1a26970-1402-40a5-8c07-406b4ba82772
-- title:
--   Freiman H5 row-2 certificate exclusions, block 1
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

theorem Freiman.lowerHistory_row2_exclusions_01 : ∀ a ∈ ([(1,287,769),(2,287,769),(4,287,769),(5,287,769),(6,287,769),(7,287,769),(1,291,887),(2,291,887),(4,291,887),(5,291,887),(1,291,900),(2,291,900),(4,291,900),(5,291,900),(6,291,905),(7,291,905),(1,291,1167),(2,291,1167),(4,291,1167),(5,291,1167),(1,293,843),(2,293,843),(4,293,843),(5,293,843),(6,293,843),(7,293,843),(1,294,890),(2,294,890),(4,294,890),(5,294,890),(1,294,902),(2,294,902),(4,294,902),(5,294,902),(6,294,903),(7,294,903),(1,294,1166),(2,294,1166),(4,294,1166),(5,294,1166),(1,429,880),(2,429,880),(4,429,880),(5,429,880),(1,429,885),(2,429,885),(4,429,885),(5,429,885),(1,429,889),(2,429,889)] : List (ℕ × ℕ × ℕ)), ∀ r s q : ℝ,
  certRectangleMem (lowerHistoryRectangles[a.1]?.getD ⟨0,1,0,1⟩) r s →
  ¬ (certBoundHolds (lowerHistoryBound a.2.1) r s q ∧
    certBoundHolds (lowerHistoryBound a.2.2) r s q) := by sorry
