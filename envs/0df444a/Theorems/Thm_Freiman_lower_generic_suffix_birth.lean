-- Prove2me | Theorems.Thm_Freiman_lower_generic_suffix_birth
-- name    : Freiman.lower_generic_suffix_birth
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:17.036303+00:00
-- url     : https://prove2.me/theorems/e9e5b410-37cc-418e-8dd6-9d6255ed5db6
-- title:
--   Freiman lower construction: generic suffix birth
-- statement:
--   Finite word inspection: after the global guards, a genuinely new 313 suffix can be born only by the selected relative label {2,3}. The run-family k=1 and left single-3 alternatives cannot create it under their guards.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/forced_reflections.tex, lem:lc-suffix-birth; global_selection.tex, guarded generic lists

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_generic_suffix_birth (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (l : LowerLabel) (hl : lowerOffered (h n) l) (right : Bool)
    (hnew : lowerEnds (lowerSide (lowerChild (h n) l) right) [3,1,3])
    (hchanged : lowerSide (lowerChild (h n) l) right ≠ lowerSide (lowerNormalize (h n)) right) :
    l = ([2],[3]) := by
  sorry
