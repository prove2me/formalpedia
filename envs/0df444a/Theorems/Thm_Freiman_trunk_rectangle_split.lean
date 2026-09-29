-- Prove2me | Theorems.Thm_Freiman_trunk_rectangle_split
-- name    : Freiman.trunk_rectangle_split
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:39:14.756138+00:00
-- url     : https://prove2.me/theorems/abcf0ff4-a360-4fcb-95a6-0b96ef79d6c3
-- title:
--   trunk rectangle split
-- statement:
--   The two printed midpoint subrectangles cover the original closed rectangle and are both nondegenerate; the shared boundary is retained.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_rectangle_split (R : CertRectangle) (axis : Bool) (hR : certRectangleValid R) (r s : ℝ) (hm : certRectangleMem R r s) :
    (certRectangleValid (trunkRectangleHalf R axis false) ∧ certRectangleValid (trunkRectangleHalf R axis true)) ∧
    (certRectangleMem (trunkRectangleHalf R axis false) r s ∨ certRectangleMem (trunkRectangleHalf R axis true) r s) := by
  sorry
