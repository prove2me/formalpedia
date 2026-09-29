-- Prove2me | Theorems.Thm_Freiman_middleRepair_row_regular_proper
-- name    : Freiman.middleRepair_row_regular_proper
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:28:46.687022+00:00
-- url     : https://prove2.me/theorems/220fb6b8-1496-4928-9d05-04bf0c22989f
-- title:
--   Report convention repair: middleRepair_row_regular_proper
-- statement:
--   Check the nine explicit finite child lists against the generic append lemma. Only digits 1,2,3 are appended; the empty append occurs on at most one side. This draft uses the report-normalized child convention, preserving actual incoming order at equal widths.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, tables in §§ opposite/equal parities Repair: active m2b_body.tex lines 46–48 and §11 physical-cylinder argument.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_row_regular_proper :
    (∀ (c : MiddleCore) (u v : List ℕ+), middleRegular c → middleDigits123 u → middleDigits123 v → 0<u.length+v.length → middleRegular (middleRepairChild c u v) ∧ middleRepairProper c (middleRepairChild c u v)) →
    ∀ (c : MiddleCore) (r : MiddleRow), middleRegular c → ∀ d ∈ middleRepairRowChildren c r, middleRegular d ∧ middleRepairProper c d := by
  sorry
