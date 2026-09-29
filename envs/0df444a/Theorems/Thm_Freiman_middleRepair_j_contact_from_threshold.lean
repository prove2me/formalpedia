-- Prove2me | Theorems.Thm_Freiman_middleRepair_j_contact_from_threshold
-- name    : Freiman.middleRepair_j_contact_from_threshold
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:29:48.702889+00:00
-- url     : https://prove2.me/theorems/ca2149ce-f63d-4347-b095-b342123ed60a
-- title:
--   Report convention repair: middleRepair_j_contact_from_threshold
-- statement:
--   Using the proved original-side orientation, translate the strict threshold comparison into the appropriate odd/even inner endpoint overlap, and prove the opposite cross comparison componentwise; both are needed for a genuine intersection. This draft uses the report-normalized child convention, preserving actual incoming order at equal widths.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:sec:jfamily following m2b:eq:jkthreshold Repair: active m2b_body.tex lines 46–48 and §11 physical-cylinder argument.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_j_contact_from_threshold :
    (∀ (p s : ℝ) (k : ℕ), p ∈ Set.Icc (1/4:ℝ) (4/5) → s ∈ Set.Icc (1/4:ℝ) (4/5) → 1 ≤ k → middleHStar p s < middleJThreshold p s k) →
    (∀ (c : MiddleCore) (r : MiddleRow) (k : ℕ), middleRegular c → middleRowCondition c r → middleEssentialJ r = true → 1 ≤ k → 1 < middleWidth ((middleNormalized c).left ++ List.replicate k 3) / middleWidth ((middleNormalized c).right ++ List.replicate k 3)) →
    ∀ (c : MiddleCore) (r : MiddleRow) (k : ℕ), middleRegular c → middleRowCondition c r → middleEssentialJ r = true → 1 ≤ k →
      (middleCover (middleRepairJ c k) ∩ middleCover (middleRepairJ c (k+2))).Nonempty := by
  sorry
