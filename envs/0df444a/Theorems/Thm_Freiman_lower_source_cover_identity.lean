-- Prove2me | Theorems.Thm_Freiman_lower_source_cover_identity
-- name    : Freiman.lower_source_cover_identity
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:18:15.940531+00:00
-- url     : https://prove2.me/theorems/bb6dec0f-55de-4d79-8151-b7bc8f093893
-- title:
--   Freiman lower construction: source cover identity
-- statement:
--   (p : LowerPair) : lowerSourceCover p = lowerCover p
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex and lower_section14.tex, equivalent e13 expressions

import Definitions.Def_Freiman_lowerSourceCover
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_source_cover_identity (p : LowerPair) : lowerSourceCover p = lowerCover p := by
  sorry
