-- Prove2me | Theorems.Thm_Freiman_lower_other22_ancestry
-- name    : Freiman.lower_other22_ancestry
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:20:36.429382+00:00
-- url     : https://prove2.me/theorems/dead2b86-b301-4d26-bd6d-6f73ace020c2
-- title:
--   Freiman lower construction: other22 ancestry
-- statement:
--   (t : ℝ) (h : ℕ → LowerPair) (m : ℕ)
--       (hh : lowerHistory t h (m+3))
--       (hg : LowerOther22Geometry (h m) (h (m+1)) (h (m+2)) (h (m+3))) :
--       lowerOther22Reached t (h (m+3))
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/other22_target.tex, lem:old23-other22-target

import Definitions.Def_Freiman_lowerOther22
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_other22_ancestry (t : ℝ) (h : ℕ → LowerPair) (m : ℕ)
    (hh : lowerHistory t h (m+3))
    (hg : LowerOther22Geometry (h m) (h (m+1)) (h (m+2)) (h (m+3))) :
    lowerOther22Reached t (h (m+3)) := by
  sorry
