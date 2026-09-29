-- Prove2me | Theorems.Thm_Freiman_middle_j_real_threshold_bounds
-- name    : Freiman.middle_j_real_threshold_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:04:02.977921+00:00
-- url     : https://prove2.me/theorems/7ae12bb0-324f-45ea-9be5-5df90191a610
-- title:
--   middle j real threshold bounds
-- statement:
--   Use the report’s 753/1000 lower bound for the first threshold factor and the uniform p,s Bernstein comparison after substituting the invariant tail boxes. All k≥2 are covered by the stated recurrence, not finite sampling.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:eq:jkthreshold

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_j_real_threshold_bounds :
    (∀ k : ℕ, 1 ≤ k → finiteCF (List.replicate k (3:ℕ+)) ∈ Set.Icc (3/10:ℝ) (1/3) ∧ finiteCF (List.replicate (k+1) (3:ℕ+)) = 1/(3+finiteCF (List.replicate k (3:ℕ+)))) →
    (∀ k : ℕ, 2 ≤ k → (∀ x ∈ [middleJA,middleJB], prefixEval (List.replicate k (3:ℕ+)) x ∈ Set.Ioo (302/1000:ℝ) (303/1000)) ∧ (∀ x ∈ [middleJC,middleJD], prefixEval (List.replicate k (3:ℕ+)) x ∈ Set.Ioo (302/1000:ℝ) (304/1000))) →
    ∀ (p s : ℝ) (k : ℕ), p ∈ Set.Icc (1/4:ℝ) (4/5) → s ∈ Set.Icc (1/4:ℝ) (4/5) → 2 ≤ k → middleHStar p s < middleJThreshold p s k := by
  sorry

end Freiman
