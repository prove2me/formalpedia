-- Prove2me | Theorems.Thm_Freiman_trunk_parameter_state
-- name    : Freiman.trunk_parameter_state
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T15:01:26.120875+00:00
-- url     : https://prove2.me/theorems/973c1522-4516-49fd-b7be-8ec4d4ba68be
-- title:
--   trunk parameter state
-- statement:
--   Admissible equal-parity parent suffixes choose one of1,2,3,31 on each side, with31 overriding1; the actual denominator ratios lie in that source rectangle.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_parameter_state (t : ℝ) (p : LowerPair) (hs : lowerState t p) (he : ¬ lowerMixed p) :
    ∃ k : Fin 16, lowerHistoryContextFits (lowerNormalize p) (trunkCatalog.states k).context ∧
    certRectangleMem (trunkCatalog.states k).rectangle (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) := by
  sorry
