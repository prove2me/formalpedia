-- Prove2me | Theorems.Thm_Freiman_lower_initial_cover
-- name    : Freiman.lower_initial_cover
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:14:59.229325+00:00
-- url     : https://prove2.me/theorems/f2b18c8a-ac7b-4422-97b6-a68a3bbf8549
-- title:
--   Freiman lower construction: initial cover
-- statement:
--   : Set.Icc cF (Real.sqrt 21) ⊆ lowerInitialSet
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, initial interval coverage

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_initial_cover : Set.Icc cF (Real.sqrt 21) ⊆ lowerInitialSet := by
  sorry
