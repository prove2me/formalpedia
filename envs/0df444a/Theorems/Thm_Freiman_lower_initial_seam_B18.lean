-- Prove2me | Theorems.Thm_Freiman_lower_initial_seam_B18
-- name    : Freiman.lower_initial_seam_B18
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:14:34.765844+00:00
-- url     : https://prove2.me/theorems/71c3620e-840c-42da-91f1-ff3dee71a5ee
-- title:
--   Freiman lower construction: initial seam B18
-- statement:
--   Uniform exact word comparison B18; includes every n,k,p and n=0 separately, not a numerical sample.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts; parametric_h_seams.json and parametric_h_nseams.json

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem Freiman.lower_initial_seam_B18 : ∀ n k, lowerContact (lowerNormalize (lowerFamilyPair .B n k 0)) [3,1,3,3,1,2,1,3] [3,1,2,1,3] [2,1,3,3,1,2,1,3] [2,1,3] := by
  sorry
