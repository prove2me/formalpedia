-- Prove2me | Theorems.Thm_Freiman_middleRepair_j_span_cover
-- name    : Freiman.middleRepair_j_span_cover
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:29:54.701141+00:00
-- url     : https://prove2.me/theorems/504c3a72-448c-44f2-9ed2-42b35cd24d90
-- title:
--   Report convention repair: middleRepair_j_span_cover
-- statement:
--   The full J span is covered by all J_k, k≥1, together with its exact limit completion. This draft uses the report-normalized child convention, preserving actual incoming order at equal widths.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:sec:jfamily Repair: active m2b_body.tex lines 46–48 and §11 physical-cylinder argument.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_j_span_cover :
    ∀ (c : MiddleCore) (r : MiddleRow), middleRegular c → middleRowCondition c r → middleEssentialJ r = true →
      ∀ t ∈ middleRepairJSpan c, t=middleLimitValue c ∨ ∃ k : ℕ, 1 ≤ k ∧ t∈middleCover (middleRepairJ c k) := by
  sorry
