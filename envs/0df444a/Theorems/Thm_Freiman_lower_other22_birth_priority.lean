-- Prove2me | Theorems.Thm_Freiman_lower_other22_birth_priority
-- name    : Freiman.lower_other22_birth_priority
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:20:45.689916+00:00
-- url     : https://prove2.me/theorems/26345117-b085-4f12-a26c-13a963d67740
-- title:
--   Freiman lower construction: other22 birth priority
-- statement:
--   Cancel the actual appended finite words to identify the already selected birth label C23, then use the corresponding earlier stored priority. No future target selection is assumed.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/other22_target.tex, lem:old23-other22-target

import Definitions.Def_Freiman_lowerOther22
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_other22_birth_priority (t : ℝ) (h : ℕ → LowerPair) (m : ℕ)
    (hh : lowerHistory t h (m+3))
    (hg : LowerOther22Geometry (h m) (h (m+1)) (h (m+2)) (h (m+3))) :
    lowerPriority t (h m) ([2],[3]) := by
  sorry
