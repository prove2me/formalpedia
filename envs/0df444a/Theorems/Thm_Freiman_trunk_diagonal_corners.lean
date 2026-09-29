-- Prove2me | Theorems.Thm_Freiman_trunk_diagonal_corners
-- name    : Freiman.trunk_diagonal_corners
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:36:14.544852+00:00
-- url     : https://prove2.me/theorems/d0610e53-40e4-4236-8dbe-163caab91318
-- title:
--   trunk diagonal corners
-- statement:
--   The literal positive printed margins and directed radical enclosures give the signed quotient value at all four source corners.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_diagonal_corners (C : TrunkCatalog) (w : TrunkWitness)
    (hw : trunkWitnessValid C w) (hn : w.diagonal ≠ 0) :
    ∀ i j : Fin 2, 0 < (w.diagonal : ℝ)*(certFieldVal (trunkPolynomial C w 1 0)+
    certFieldVal (trunkPolynomial C w 2 0)*((trunkCorner w.rectangle.r0 w.rectangle.r1 i : ℝ)+trunkCorner w.rectangle.s0 w.rectangle.s1 j)+
    certFieldVal (trunkPolynomial C w 2 1)*trunkCorner w.rectangle.r0 w.rectangle.r1 i*trunkCorner w.rectangle.s0 w.rectangle.s1 j) := by
  sorry
