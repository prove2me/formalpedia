-- Prove2me | Theorems.Thm_Freiman_lower_initial_seam_C
-- name    : Freiman.lower_initial_seam_C
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:14:31.913503+00:00
-- url     : https://prove2.me/theorems/6e77a95a-b437-4b45-9bd1-d60032f56d13
-- title:
--   Freiman lower construction: initial seam C
-- statement:
--   Uniform exact word comparison C; includes every n,k,p and n=0 separately, not a numerical sample.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts; parametric_h_seams.json and parametric_h_nseams.json

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem Freiman.lower_initial_seam_C : ∀ n k p, lowerContact (lowerNormalize (lowerFamilyPair .C n k p)) [3,3,1,2,1,3] [3,1,2,1,3] [3,3,1,2,1,3] [2,1,3] := by
  sorry
