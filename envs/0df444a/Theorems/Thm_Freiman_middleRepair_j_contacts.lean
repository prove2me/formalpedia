-- Prove2me | Theorems.Thm_Freiman_middleRepair_j_contacts
-- name    : Freiman.middleRepair_j_contacts
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:29:55.868398+00:00
-- url     : https://prove2.me/theorems/b614e25c-cc50-4753-833c-266675511e98
-- title:
--   Report convention repair: middleRepair_j_contacts
-- statement:
--   The odd and even J subfamilies each form a chain, with every k linked to k+2. This draft uses the report-normalized child convention, preserving actual incoming order at equal widths.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:sec:jfamily Repair: active m2b_body.tex lines 46–48 and §11 physical-cylinder argument.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_j_contacts :
    ∀ (c : MiddleCore) (r : MiddleRow) (k : ℕ), middleRegular c → middleRowCondition c r → middleEssentialJ r = true → 1 ≤ k →
      (middleCover (middleRepairJ c k) ∩ middleCover (middleRepairJ c (k+2))).Nonempty := by
  sorry
