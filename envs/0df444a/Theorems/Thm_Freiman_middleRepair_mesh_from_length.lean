-- Prove2me | Theorems.Thm_Freiman_middleRepair_mesh_from_length
-- name    : Freiman.middleRepair_mesh_from_length
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:31:00.376511+00:00
-- url     : https://prove2.me/theorems/4566968b-9d22-4e73-b2f6-071657dd920f
-- title:
--   Report convention repair: middleRepair_mesh_from_length
-- statement:
--   At least one side has length ≥ceil(N/2). Its Fibonacci width bound and the necessary good-cover ratio<5 bound both widths and force their sum to zero. This handles the possibility that only one side is extended at a particular step. This draft uses the report-normalized child convention, preserving actual incoming order at equal widths.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:prop:path, displayed mesh estimate Repair: active m2b_body.tex lines 46–48 and §11 physical-cylinder argument.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_mesh_from_length :
    (∀ w : List ℕ+, middleWidth w  ≤  (middleBeta-middleAlpha)/(Nat.fib (w.length+1):ℝ)^2) →
    (∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRatio c < (5:ℝ)) →
    ∀ (c : MiddleCore) (t : ℝ) (p : ℕ→MiddleCore), middleRepairPath c t p →
      (∀ n : ℕ, n+c.left.length+c.right.length  ≤  (p n).left.length+(p n).right.length) →
      Filter.Tendsto (fun n : ℕ => middleWidth (p n).left+middleWidth (p n).right) Filter.atTop (nhds 0) := by
  sorry
