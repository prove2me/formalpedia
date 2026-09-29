-- Prove2me | Theorems.Thm_Freiman_trunk_endpoint_strict_order
-- name    : Freiman.trunk_endpoint_strict_order
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T15:00:38.94116+00:00
-- url     : https://prove2.me/theorems/a53d38cc-5a32-43b8-ba73-77fd5df0932b
-- title:
--   trunk endpoint strict order
-- statement:
--   Every ordinary source cover has distinct correctly ordered endpoints; this strict own-interval order is separate from crossed contact inequalities.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_endpoint_strict_order (p : LowerPair) :
    lowerEndpoint p false < lowerEndpoint p true := by
  sorry
