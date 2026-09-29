-- Prove2me | Theorems.Thm_Freiman_trunk_diagonal_factor
-- name    : Freiman.trunk_diagonal_factor
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:36:09.186887+00:00
-- url     : https://prove2.me/theorems/c59a3cea-75be-441d-b7cc-9452b933fb19
-- title:
--   trunk diagonal factor
-- statement:
--   Exact antisymmetry of the3×3 coefficient matrix factors its polynomial by r−s; the quotient is the source bilinear expression.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_diagonal_factor (P : CertPoly22) (hs : ∀ i j : Fin 3, P i j = certFieldScale (-1) (P j i)) (r s : ℝ) :
    certPolyEval P r s = (r-s)*(certFieldVal (P 1 0)+certFieldVal (P 2 0)*(r+s)+certFieldVal (P 2 1)*r*s) := by
  sorry
