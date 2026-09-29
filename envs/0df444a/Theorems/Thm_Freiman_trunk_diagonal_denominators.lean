-- Prove2me | Theorems.Thm_Freiman_trunk_diagonal_denominators
-- name    : Freiman.trunk_diagonal_denominators
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:38:05.614455+00:00
-- url     : https://prove2.me/theorems/ddb77160-b6e3-49bf-9874-2e1e01ddc1cd
-- title:
--   trunk diagonal denominators
-- statement:
--   Nonnegative source r and denominator tails make both diagonal-pair denominators strictly positive.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_diagonal_denominators (C : TrunkCatalog) (w : TrunkWitness) (hw : trunkWitnessValid C w) (hn : w.diagonal ≠ 0)
    (r s : ℝ) (hm : certRectangleMem w.rectangle r s) :
    0 < certThresholdDen (trunkBound C w.lowerId).threshold r ∧ 0 < certThresholdDen (trunkBound C w.upperId).threshold r := by
  sorry
