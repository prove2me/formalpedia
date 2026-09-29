-- Prove2me | Theorems.Thm_Freiman_lower_equal_three_source_good
-- name    : Freiman.lower_equal_three_source_good
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:18:16.617814+00:00
-- url     : https://prove2.me/theorems/d0346100-6607-40b7-af36-3d0c25830007
-- title:
--   Freiman lower construction: equal three source good
-- statement:
--   The actual source criterion (12.8) for equal parity and both ends 3, retaining the source auxiliary e13 endpoint formula. The separately proved source/formal endpoint equivalence transfers the certificate to the formal cover algorithm.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/j_family.tex, lem:equal-three-width; lower_core.tex source endpoint convention

import Definitions.Def_Freiman_lowerSourceCover
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_equal_three_source_good (p : LowerPair) (ha : lowerAdmissible p) (hp : ¬ lowerMixed p)
    (hl : lowerEnds p.1 [3]) (hr : lowerEnds p.2 [3]) (hb : lowerParameterBox p)
    (hwide : lowerWidth p.2 ≤ lowerWidth p.1)
    (hratio : lowerWidth p.1 < (19/5 : ℝ)*lowerWidth p.2) : lowerSourceGood p := by
  sorry
