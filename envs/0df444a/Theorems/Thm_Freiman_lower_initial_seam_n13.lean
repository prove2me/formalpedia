-- Prove2me | Theorems.Thm_Freiman_lower_initial_seam_n13
-- name    : Freiman.lower_initial_seam_n13
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:14:48.498375+00:00
-- url     : https://prove2.me/theorems/dad9a8cc-7960-43da-bc6f-fd942c7b7021
-- title:
--   Freiman lower construction: initial seam n13
-- statement:
--   Uniform exact word comparison n13; includes every n,k,p and n=0 separately, not a numerical sample.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts; parametric_h_seams.json and parametric_h_nseams.json

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem Freiman.lower_initial_seam_n13 : ∀ n, lowerNContact n [3,1,3,1,2,3,1,2,1,3] [3,1,3,3,1,2,1,3] [3,1,3,1,2,1,3] [3,1,2,1,3] := by
  sorry
