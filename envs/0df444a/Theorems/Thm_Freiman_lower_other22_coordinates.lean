-- Prove2me | Theorems.Thm_Freiman_lower_other22_coordinates
-- name    : Freiman.lower_other22_coordinates
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:20:35.717881+00:00
-- url     : https://prove2.me/theorems/a7a3bdee-659b-411a-ae77-6a12a29c1a8d
-- title:
--   Freiman lower construction: other22 coordinates
-- statement:
--   The three selected physical additions and strict middle reflection preserve the birth equal parity at the final normalized S. This establishes the same signed scalar coordinate, including opposite parity.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/other22_target.tex, lem:old23-other22-target

import Definitions.Def_Freiman_lowerOther22
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_other22_coordinates (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S) (t : ℝ) : lowerLocalCoordinate S t = lowerLocalCoordinate Z t := by
  sorry
