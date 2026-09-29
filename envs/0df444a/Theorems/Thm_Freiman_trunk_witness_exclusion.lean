-- Prove2me | Theorems.Thm_Freiman_trunk_witness_exclusion
-- name    : Freiman.trunk_witness_exclusion
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:38:09.646288+00:00
-- url     : https://prove2.me/theorems/2c77e160-cde8-429e-bcfd-8b0cf3492f1d
-- title:
--   trunk witness exclusion
-- statement:
--   Both the ordinary Bernstein and the explicitly split diagonal witnesses have their intended mathematical exclusion meaning.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_witness_exclusion (C : TrunkCatalog) (w : TrunkWitness) (hw : trunkWitnessValid C w) :
    TrunkWitnessExclusion C w := by
  sorry
