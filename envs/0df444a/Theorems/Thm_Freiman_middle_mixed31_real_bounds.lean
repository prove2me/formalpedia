-- Prove2me | Theorems.Thm_Freiman_middle_mixed31_real_bounds
-- name    : Freiman.middle_mixed31_real_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:03:54.680995+00:00
-- url     : https://prove2.me/theorems/c1ac44a9-5c2c-4958-aae8-27cf4ad9e5d6
-- title:
--   middle mixed31 real bounds
-- statement:
--   The two strict biquadratic comparisons P>0 and Q>0 on the full real rectangle, certified by their nine tensor Bernstein coefficients. They are the uniform source of the C31 width estimate.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:eq:mixed31coefficients

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_mixed31_real_bounds :
    ∀ p s : ℝ, p ∈ Set.Icc (1/4:ℝ) (4/5) → s ∈ Set.Icc (1/4:ℝ) (4/5) →
      middleScalarA p s (55/100) < (19/5:ℝ)*middleMixedK p s ∧
      (5/19:ℝ)*middleMixedK p s < middleScalarB p s (328/1000) := by
  sorry

end Freiman
