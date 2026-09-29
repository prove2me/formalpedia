-- Prove2me | Theorems.Thm_Freiman_trunk_diagonal_exclusion
-- name    : Freiman.trunk_diagonal_exclusion
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:37:02.259415+00:00
-- url     : https://prove2.me/theorems/23e45fd7-ad7e-4b82-9489-0a8a08e7d44b
-- title:
--   trunk diagonal exclusion
-- statement:
--   A diagonal pair excludes its q-premises even on r=s because at least one q-bound is strict.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_diagonal_exclusion (C : TrunkCatalog) (w : TrunkWitness) (hw : trunkWitnessValid C w) (hn : w.diagonal ≠ 0) :
    TrunkWitnessExclusion C w := by
  sorry
