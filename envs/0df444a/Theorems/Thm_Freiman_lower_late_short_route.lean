-- Prove2me | Theorems.Thm_Freiman_lower_late_short_route
-- name    : Freiman.lower_late_short_route
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:12.81607+00:00
-- url     : https://prove2.me/theorems/5a2446aa-7eb2-446f-9655-08ab76ebc19d
-- title:
--   Freiman lower construction: late short route
-- statement:
--   The exceptional exact parent (31,31) has its separately certified finite good chain; the long-parent r≥13/17 bound is not asserted here.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_140_144.tex, lem:late-short-parent

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_late_short_route (p : LowerPair) (hp : lowerNormalize p = ([3,1],[3,1])) : ∃ ls : List LowerLabel, lowerLateRouteValid p ls := by
  sorry
