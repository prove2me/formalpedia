-- Prove2me | Theorems.Thm_Freiman_lower_equal_three_good
-- name    : Freiman.lower_equal_three_good
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:18:03.754781+00:00
-- url     : https://prove2.me/theorems/b8d53c1d-4f04-4d69-8b6b-b55c54e1b071
-- title:
--   Freiman lower construction: equal three good
-- statement:
--   The actual equal-parity, both-ending-in-3 cover is good under full-width ratio <19/5, using the exact two rational-product estimates and endpoint comparisons from the source criterion.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/j_family.tex, lem:equal-three-width

import Definitions.Def_Freiman_lowerSourceCover
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_equal_three_good (p : LowerPair) (ha : lowerAdmissible p) (hp : ¬ lowerMixed p)
    (hl : lowerEnds p.1 [3]) (hr : lowerEnds p.2 [3]) (hb : lowerParameterBox p)
    (hwide : lowerWidth p.2 ≤ lowerWidth p.1)
    (hratio : lowerWidth p.1 < (19/5 : ℝ)*lowerWidth p.2) : lowerGood p := by
  sorry
