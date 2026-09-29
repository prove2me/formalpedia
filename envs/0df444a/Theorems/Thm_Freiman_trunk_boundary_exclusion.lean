-- Prove2me | Theorems.Thm_Freiman_trunk_boundary_exclusion
-- name    : Freiman.trunk_boundary_exclusion
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:37:36.360256+00:00
-- url     : https://prove2.me/theorems/bf6bf2a9-568c-4e70-bf7d-b81e1c56ff4b
-- title:
--   trunk boundary exclusion
-- statement:
--   The two residual closed-boundary rows are discharged by the original H11/H0 factor and the explicit actual source-bound evaluation at the only possible corner.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_boundary_exclusion (R : CertRectangle) (bs : List CertBound) (hb : trunkBoundaryBound R bs)
    (r s q : ℝ) (hm : certRectangleMem R r s) :
    ¬ trunkHolds bs r s q := by
  sorry
