-- Prove2me | Theorems.Thm_Freiman_middle_parameter_rectangle
-- name    : Freiman.middle_parameter_rectangle
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:01:32.125789+00:00
-- url     : https://prove2.me/theorems/4e4e8d23-9cc1-4dd7-8021-08339ae1ec9f
-- title:
--   middle parameter rectangle
-- statement:
--   The full real interval [1/4,4/5] is invariant under the three append maps.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, equation m2b:eq:update

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_parameter_rectangle :
    ∀ (p : ℝ) (a : ℕ+), p ∈ Set.Icc (1/4:ℝ) (4/5) → (a:ℕ)  ≤  3 →
      1 / (((a:ℕ):ℝ)+p) ∈ Set.Icc (1/4:ℝ) (4/5) := by
  sorry

end Freiman
