-- Prove2me | Theorems.Thm_Freiman_middle_j_recurrence
-- name    : Freiman.middle_j_recurrence
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:03:59.162978+00:00
-- url     : https://prove2.me/theorems/0366ddf8-79c7-4914-85c7-46f34e9923bd
-- title:
--   middle j recurrence
-- statement:
--   The symmetric 3^k continuant parameter has base values 1/3,3/10 and invariant interval [3/10,1/3].
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:sec:jfamily, recurrence for r_k

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_j_recurrence :
    ∀ k : ℕ, 1 ≤ k →
      finiteCF (List.replicate k (3:ℕ+)) ∈ Set.Icc (3/10:ℝ) (1/3) ∧
      finiteCF (List.replicate (k+1) (3:ℕ+)) = 1/(3+finiteCF (List.replicate k (3:ℕ+))) := by
  sorry

end Freiman
