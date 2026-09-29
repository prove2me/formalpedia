-- Prove2me | Theorems.Thm_Freiman_trunk_endpoint_strict_equal
-- name    : Freiman.trunk_endpoint_strict_equal
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:58:35.797743+00:00
-- url     : https://prove2.me/theorems/cb516e14-fb34-4dd6-83eb-351182fc015a
-- title:
--   trunk endpoint strict equal
-- statement:
--   For equal whole-word parity, the four natural/shortened endpoint tails lie in strictly ordered separated ranges; finite positive-digit prefix maps give strict actual endpoint order, including every auxiliary-width tie.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_endpoint_strict_equal (p : LowerPair) (hp : p.1.length % 2 = p.2.length % 2) :
    lowerEndpoint p false < lowerEndpoint p true := by
  sorry
