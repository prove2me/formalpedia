-- Prove2me | Theorems.Thm_Freiman_lower_other22_exclusion_upper
-- name    : Freiman.lower_other22_exclusion_upper
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:20:30.677318+00:00
-- url     : https://prove2.me/theorems/282f35c1-8d12-4e8e-bb7b-9763bd6e3c6b
-- title:
--   Freiman lower construction: other22 exclusion upper
-- statement:
--   A point above the actual child lower endpoint but outside the actual closed child interval must be above its upper endpoint; scalar parity is handled explicitly.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/other22_target.tex, lem:old23-other22-target

import Definitions.Def_Freiman_lowerOther22
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_other22_exclusion_upper (Z : LowerPair) (t : ℝ)
    (hnot : t ∉ lowerCover (lowerChild Z ([3],[2])))
    (hlo : lowerLocalLower Z ([3],[2]) < lowerLocalCoordinate Z t) :
    lowerChildUpper Z ([3],[2]) < lowerLocalCoordinate Z t := by
  sorry
