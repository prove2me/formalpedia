-- Prove2me | Theorems.Thm_Freiman_trunk_boundary_polynomial_order
-- name    : Freiman.trunk_boundary_polynomial_order
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:39:23.119734+00:00
-- url     : https://prove2.me/theorems/031dc69e-5f2b-47f8-a9e7-ba6683d0a6af
-- title:
--   trunk boundary polynomial order
-- statement:
--   Retain the equality case of the original H11/H0 polynomial instead of applying a strict q-premise that no longer holds at the incoming-frame boundary.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_boundary_polynomial_order (hc : trunkBoundaryCertificateValid) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r ≤ s)
    (hp : certPolyEval trunkBoundaryPolynomial r s ≤ 0) :
    r = s := by
  sorry
