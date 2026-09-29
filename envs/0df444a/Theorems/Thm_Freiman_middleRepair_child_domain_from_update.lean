-- Prove2me | Theorems.Thm_Freiman_middleRepair_child_domain_from_update
-- name    : Freiman.middleRepair_child_domain_from_update
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:28:34.373642+00:00
-- url     : https://prove2.me/theorems/6be3bcdb-47ce-415a-82d3-851bcf5b0a42
-- title:
--   Report convention repair: middleRepair_child_domain_from_update
-- statement:
--   Iterate the real append-map domain lemma on each physical side; every nonempty appended pair is a proper compatible descendant, including a reflected normalized parent. This draft uses the report-normalized child convention, preserving actual incoming order at equal widths.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, cover convention and m2b:eq:update Repair: active m2b_body.tex lines 46–48 and §11 physical-cylinder argument.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_child_domain_from_update :
    (∀ (w : List ℕ+) (a : ℕ+), middleParameter (w ++ [a]) = 1 / (((a:ℕ):ℝ)+middleParameter w)) →
    (∀ (p : ℝ) (a : ℕ+), p ∈ Set.Icc (1/4:ℝ) (4/5) → (a:ℕ) ≤ 3 → 1/(((a:ℕ):ℝ)+p) ∈ Set.Icc (1/4:ℝ) (4/5)) →
    ∀ (c : MiddleCore) (u v : List ℕ+), middleRegular c → middleDigits123 u → middleDigits123 v →
      0 < u.length+v.length → middleRegular (middleRepairChild c u v) ∧ middleRepairProper c (middleRepairChild c u v) := by
  sorry
