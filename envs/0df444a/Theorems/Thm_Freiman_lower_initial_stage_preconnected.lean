-- Prove2me | Theorems.Thm_Freiman_lower_initial_stage_preconnected
-- name    : Freiman.lower_initial_stage_preconnected
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-09-12T13:05:55.83031+00:00
-- url     : https://prove2.me/theorems/647e259f-6665-4932-bf0d-865e7b491b08
-- title:
--   Freiman lower construction: one initial stage is preconnected
-- statement:
--   Fix a period index $n$. Assuming the complete initial seam package and the endpoint-limit package, the stage containing all $A$, $B$, and $C$ intervals at index $n$, their displayed limiting values, and the auxiliary $B$ interval is preconnected. This is the within-stage topological gluing obligation for the initial lower construction.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, proof of prop:lc-H-contacts; derived within-stage gluing lemma.

import Definitions.Def_Freiman_lowerInitialStage

open Freiman

theorem Freiman.lower_initial_stage_preconnected
    (hseams : lowerInitialSeams) (hlimits : lowerInitialLimits) (n : ℕ) :
    IsPreconnected (lowerInitialStage n) := by
  sorry
