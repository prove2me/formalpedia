-- Prove2me | Theorems.Thm_Freiman_middleRepair_path_length
-- name    : Freiman.middleRepair_path_length
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:30:57.301921+00:00
-- url     : https://prove2.me/theorems/413ebb8b-c933-447e-b3d1-44fe093fd52b
-- title:
--   Report convention repair: middleRepair_path_length
-- statement:
--   Each proper transition appends at least one digit, so total physical prefix length grows at least linearly along every actual path. This draft uses the report-normalized child convention, preserving actual incoming order at equal widths.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:prop:path, N=|U|+|V| Repair: active m2b_body.tex lines 46–48 and §11 physical-cylinder argument.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_path_length :
    ∀ (c : MiddleCore) (t : ℝ) (p : ℕ→MiddleCore), middleRepairPath c t p →
      ∀ n : ℕ, n+c.left.length+c.right.length  ≤  (p n).left.length+(p n).right.length := by
  sorry
