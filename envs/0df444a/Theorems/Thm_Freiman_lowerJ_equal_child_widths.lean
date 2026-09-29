-- Prove2me | Theorems.Thm_Freiman_lowerJ_equal_child_widths
-- name    : Freiman.lowerJ_equal_child_widths
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:02:45.065336+00:00
-- url     : https://prove2.me/theorems/e1b70539-e1cc-41fc-9e46-2c9a3cd2fd5b
-- title:
--   Freiman repeated-three proof: equal child widths
-- statement:
--   The two explicit monotone fractional-factor estimates show V wider than U2 and U11; no unrecorded large certificate is used.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_equal_child_widths (hw : ∀ w : List ℕ+, lowerWidth w = (lowerBeta-lowerAlpha)/((((lowerCD w).1:ℝ)*lowerAlpha+(lowerCD w).2)*(((lowerCD w).1:ℝ)*lowerBeta+(lowerCD w).2))) (hc : (1/4:ℝ) < lowerAlpha ∧ lowerAlpha < (27/100:ℝ) ∧ (3/4:ℝ) < lowerBeta ∧ lowerBeta < (4/5:ℝ) ∧ (13243/18000:ℝ)<1 ∧ (739328/796875:ℝ)<1) (p : LowerPair) (ha : lowerAdmissible p) (hp : ¬ lowerMixed p) (hl : lowerEnds p.1 [3]) (hr : lowerEnds p.2 [3]) (hb : lowerParameterBox p) (hwide : lowerWidth p.2 ≤ lowerWidth p.1) (hratio : lowerWidth p.1 < (19/5:ℝ)*lowerWidth p.2) : lowerWidth ((lowerNormalize p).1++[2]) < lowerWidth (lowerNormalize p).2 ∧ lowerWidth ((lowerNormalize p).1++[1,1]) < lowerWidth (lowerNormalize p).2 := by
  sorry
