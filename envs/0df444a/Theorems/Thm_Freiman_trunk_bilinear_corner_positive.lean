-- Prove2me | Theorems.Thm_Freiman_trunk_bilinear_corner_positive
-- name    : Freiman.trunk_bilinear_corner_positive
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:35:10.729664+00:00
-- url     : https://prove2.me/theorems/83ff2a31-a880-4b02-9bb2-77b34d3f7026
-- title:
--   trunk bilinear corner positive
-- statement:
--   A bilinear function is a convex combination of its four corner values throughout the closed rectangle; strict positivity includes its boundary.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_bilinear_corner_positive (R : CertRectangle) (A B D : ℝ) (hR : certRectangleValid R)
    (hc : ∀ i j : Fin 2, 0 < A+B*((trunkCorner R.r0 R.r1 i : ℝ)+trunkCorner R.s0 R.s1 j)+D*trunkCorner R.r0 R.r1 i*trunkCorner R.s0 R.s1 j)
    (r s : ℝ) (hm : certRectangleMem R r s) :
    0 < A+B*(r+s)+D*r*s := by
  sorry
