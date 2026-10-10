-- Prove2me | Theorems.Thm_Freiman_lower_initial_stage_overlap
-- name    : Freiman.lower_initial_stage_overlap
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-09-12T13:06:01.937338+00:00
-- url     : https://prove2.me/theorems/64a6cc4a-8928-446e-86ce-33da4dbca78e
-- title:
--   Freiman lower construction: consecutive initial stages overlap
-- statement:
--   For every period index $n$, the seam package forces the stage at $n$ to meet the stage at $n+1$. This is the cross-period contact needed to chain all initial stages into one preconnected set.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, proof of prop:lc-H-contacts; derived consecutive-stage contact lemma.

import Definitions.Def_Freiman_lowerInitialStage

open Freiman

theorem Freiman.lower_initial_stage_overlap
    (hseams : lowerInitialSeams) (n : ℕ) :
    (lowerInitialStage n ∩ lowerInitialStage (n+1)).Nonempty := by
  sorry
