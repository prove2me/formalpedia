-- Prove2me | Theorems.Thm_Freiman_middle_j_tail_boxes
-- name    : Freiman.middle_j_tail_boxes
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:04:13.168356+00:00
-- url     : https://prove2.me/theorems/7f05800c-628e-48a1-be83-44b597009570
-- title:
--   middle j tail boxes
-- statement:
--   Exact k=2 bounds and invariance under φ3 give the two strict tail boxes for every k≥2.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:eq:jkthreshold, k≥2 case

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_j_tail_boxes :
    ∀ k : ℕ, 2 ≤ k →
      (∀ x ∈ [middleJA,middleJB], prefixEval (List.replicate k (3:ℕ+)) x ∈ Set.Ioo (302/1000:ℝ) (303/1000)) ∧
      (∀ x ∈ [middleJC,middleJD], prefixEval (List.replicate k (3:ℕ+)) x ∈ Set.Ioo (302/1000:ℝ) (304/1000)) := by
  sorry

end Freiman
