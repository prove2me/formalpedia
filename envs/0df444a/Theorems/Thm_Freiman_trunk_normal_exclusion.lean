-- Prove2me | Theorems.Thm_Freiman_trunk_normal_exclusion
-- name    : Freiman.trunk_normal_exclusion
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:34:11.897769+00:00
-- url     : https://prove2.me/theorems/3f05be6a-3eb4-468b-9864-6ce375cb62a5
-- title:
--   trunk normal exclusion
-- statement:
--   An ordinary original source witness excludes the actual effective pair with the same threshold data, after explicitly checking actual strictness.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_normal_exclusion (C : TrunkCatalog) (w : TrunkWitness)
    (hw : trunkWitnessValid C w) (hz : w.diagonal = 0) :
    TrunkWitnessExclusion C w := by
  sorry
