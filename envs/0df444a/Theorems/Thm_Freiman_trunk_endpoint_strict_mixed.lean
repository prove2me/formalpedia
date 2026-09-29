-- Prove2me | Theorems.Thm_Freiman_trunk_endpoint_strict_mixed
-- name    : Freiman.trunk_endpoint_strict_mixed
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T15:00:46.400796+00:00
-- url     : https://prove2.me/theorems/8729fc52-f3fc-4eb1-b214-2bc3d7700b29
-- title:
--   trunk endpoint strict mixed
-- statement:
--   For opposite whole-word parity, compare the natural endpoint with the virtual endpoint after appending1 to the actual wider side. The exact ordered tail ranges give strict endpoint order in both normalization branches, retaining the incoming side at equality.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_endpoint_strict_mixed (p : LowerPair) (hp : p.1.length % 2 ≠ p.2.length % 2) :
    lowerEndpoint p false < lowerEndpoint p true := by
  sorry
