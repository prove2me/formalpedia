-- Prove2me | Theorems.Thm_Freiman_form_second_root_eventually_reduced
-- name    : Freiman.form_second_root_eventually_reduced
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:37.720147+00:00
-- url     : https://prove2.me/theorems/2516d1b9-c747-47f7-8d2b-f48b6fca6126
-- title:
--   The second inverse root eventually lies strictly between minus one and zero
-- statement:
--   The errors p_n−rq_n tend to zero. The denominator increments tend to infinity, hence (p_(n+1)−sq_(n+1))−(p_n−sq_n)>0 eventually. Both terms are positive eventually. Their negative ratio therefore lies in (−1,0). This is the report’s explicit estimate for the second root, separated from the algebraic reconstruction.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.3, middle paragraph of found:reduce-roots

import Definitions.Def_Freiman_reducedForms
import Definitions.Def_Freiman_rootConvergentData

namespace Freiman

theorem form_second_root_eventually_reduced (r s : ℝ) (hrs : s<r) (D : RootConvergentData r) :
    ∃ N : ℕ, ∀ n : ℕ, N≤n → secondRootCoordinate D s n ∈ Set.Ioo (-1 : ℝ) 0 := by
  sorry

end Freiman
