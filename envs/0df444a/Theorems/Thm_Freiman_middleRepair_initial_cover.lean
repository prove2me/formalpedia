-- Prove2me | Theorems.Thm_Freiman_middleRepair_initial_cover
-- name    : Freiman.middleRepair_initial_cover
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:30:48.211778+00:00
-- url     : https://prove2.me/theorems/04623e8d-8bf3-4310-9b24-718d7423acd5
-- title:
--   Report convention repair: middleRepair_initial_cover
-- statement:
--   The fifteen exact initial good covers cover the entire closed target interval, with regularity and goodness supplied for every selected root. This draft uses the report-normalized child convention, preserving actual incoming order at equal widths.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:sec:initial Repair: active m2b_body.tex lines 46–48 and §11 physical-cylinder argument.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_initial_cover :
    ∀ t ∈ Set.Icc (Real.sqrt 21) (128/25:ℝ), ∃ i : Fin 15, middleRegular (middleRoot i) ∧ middleRepairGood (middleRoot i) ∧ t∈middleCover (middleRoot i) := by
  sorry
