-- Prove2me | Theorems.Thm_Freiman_lower_models
-- name    : Freiman.lower_models
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:16:13.147992+00:00
-- url     : https://prove2.me/theorems/c7903dc7-c1c6-4cf6-acee-af97d033ddf2
-- title:
--   Freiman lower construction: models
-- statement:
--   (t : ℝ) (ht : t ∈ Set.Icc cF (Real.sqrt 21)) : lowerHasValue t
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/global_selection.tex, thm:global-selection

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_models (t : ℝ) (ht : t ∈ Set.Icc cF (Real.sqrt 21)) : lowerHasValue t := by
  sorry
