-- Prove2me | Theorems.Thm_Freiman_middleRepair_j_regular_proper
-- name    : Freiman.middleRepair_j_regular_proper
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:28:48.793346+00:00
-- url     : https://prove2.me/theorems/77d5258c-24ee-4d1f-b0c8-8266abfac6b0
-- title:
--   Report convention repair: middleRepair_j_regular_proper
-- statement:
--   All J descendants append k copies of 3 to both physical sides and are proper regular descendants for every k ≥ 1. This draft uses the report-normalized child convention, preserving actual incoming order at equal widths.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:sec:jfamily Repair: active m2b_body.tex lines 46–48 and §11 physical-cylinder argument.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_j_regular_proper :
    (∀ (c : MiddleCore) (u v : List ℕ+), middleRegular c → middleDigits123 u → middleDigits123 v → 0<u.length+v.length → middleRegular (middleRepairChild c u v) ∧ middleRepairProper c (middleRepairChild c u v)) →
    ∀ (c : MiddleCore) (k : ℕ), middleRegular c → 1 ≤ k → middleRegular (middleRepairJ c k) ∧ middleRepairProper c (middleRepairJ c k) := by
  sorry
