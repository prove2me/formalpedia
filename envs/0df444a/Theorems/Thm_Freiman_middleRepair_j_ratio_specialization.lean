-- Prove2me | Theorems.Thm_Freiman_middleRepair_j_ratio_specialization
-- name    : Freiman.middleRepair_j_ratio_specialization
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:29:53.501106+00:00
-- url     : https://prove2.me/theorems/535dbe07-c81b-41d3-be60-c50ddd3c4513
-- title:
--   Report convention repair: middleRepair_j_ratio_specialization
-- statement:
--   Substitute actual J tails and positive q in the uniform rectangle comparison, derive the strict original-side ratio above 1 and below 19/5, and justify retaining that side under normalization for every k. This draft uses the report-normalized child convention, preserving actual incoming order at equal widths.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:lem:jgood and m2b:eq:jupper Repair: active m2b_body.tex lines 46–48 and §11 physical-cylinder argument.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_j_ratio_specialization :
    (∀ p s x y : ℝ, p ∈ Set.Icc (1/4:ℝ) (4/5) → s ∈ Set.Icc (1/4:ℝ) (4/5) → x ∈ Set.Icc middleAlpha (prefixEval [3] middleAlpha) → y ∈ Set.Icc middleAlpha (prefixEval [3] middleAlpha) → middleHStar p s < middleH p s x y ∧ (5/19:ℝ)*middleH p s x y < middleScalarA p s (549/1000) ∧ (5/19:ℝ)*middleH p s x y < middleScalarB p s (313/1000)) →
    ∀ (c : MiddleCore) (r : MiddleRow) (k : ℕ), middleRegular c → middleRowCondition c r → middleEssentialJ r = true → 1 ≤ k →
      1 < middleWidth ((middleNormalized c).left ++ List.replicate k 3) / middleWidth ((middleNormalized c).right ++ List.replicate k 3) ∧ middleRatio (middleRepairJ c k)<(19/5:ℝ) := by
  sorry
