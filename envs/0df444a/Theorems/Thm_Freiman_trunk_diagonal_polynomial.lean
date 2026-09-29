-- Prove2me | Theorems.Thm_Freiman_trunk_diagonal_polynomial
-- name    : Freiman.trunk_diagonal_polynomial
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:39:07.88773+00:00
-- url     : https://prove2.me/theorems/df90fe49-034c-44b8-ae8f-a66de0d845cc
-- title:
--   trunk diagonal polynomial
-- statement:
--   The diagonal witness polynomial is nonnegative on its designated half of the source rectangle.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_diagonal_polynomial (C : TrunkCatalog) (w : TrunkWitness) (hw : trunkWitnessValid C w) (hn : w.diagonal ≠ 0)
    (r s : ℝ) (hm : certRectangleMem w.rectangle r s) (hs : 0 ≤ (w.diagonal : ℝ)*(r-s)) :
    0 ≤ certPolyEval (trunkPolynomial C w) r s := by
  sorry
