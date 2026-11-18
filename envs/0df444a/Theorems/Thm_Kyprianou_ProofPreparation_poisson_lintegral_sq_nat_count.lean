-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_lintegral_sq_nat_count
-- name    : Kyprianou.ProofPreparation.poisson_lintegral_sq_nat_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:37:50.268481+00:00
-- url     : https://prove2.me/theorems/644bbdb1-c4ba-43dc-89a2-94d50c8a772f
-- title:
--   Poisson-count second moment as an extended nonnegative integral
-- statement:
--   For a Poisson law with finite rate r, its squared natural count has extended nonnegative second moment equal to r squared plus r. Adapt the Proved Poisson series identity to the ENNReal integral used in Chapter 2 Theorem 2.7's second-moment proof.
-- source:
--   Kyprianou (2006), Chapter 2 Theorem 2.7, Poisson count second moment step; LeanLevy PoissonSecondMoment_hasSum.

import Mathlib
import Theorems.Thm_ProbabilityTheory_poissonSecondMoment_hasSum
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Nat
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_lintegral_sq_nat_count (r : ℝ≥0) :
  (∫⁻ n : ℕ, ENNReal.ofReal ((n : ℝ) ^ 2) ∂(poissonMeasure r)) =
    ENNReal.ofReal ((r : ℝ) ^ 2 + r) := by sorry
end Kyprianou.ProofPreparation
