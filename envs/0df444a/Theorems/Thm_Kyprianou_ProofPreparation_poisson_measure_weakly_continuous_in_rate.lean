-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_measure_weakly_continuous_in_rate
-- name    : Kyprianou.ProofPreparation.poisson_measure_weakly_continuous_in_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T23:52:40.2324+00:00
-- url     : https://prove2.me/theorems/60211709-1937-4ef6-8630-797affd5e5f8
-- title:
--   Weak continuity of real-valued Poisson laws under convergence of the intensity
-- statement:
--   For any convergent sequence of nonnegative Poisson intensities, the probability measures of the corresponding real-valued Poisson counts converge weakly to the Poisson law with limiting intensity, established by their pointwise characteristic functions.
-- source:
--   Kyprianou (2006), Chapter 2 Exercise 2.1, convergence of Poisson random variables and intensity sequences.

import Mathlib
import Definitions.Def_Kyprianou_ProofPreparation_realPoissonProbability
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal Nat Topology
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
noncomputable section
theorem poisson_measure_weakly_continuous_in_rate
    (rate : ℕ → ℝ≥0) (r : ℝ≥0)
    (hrate : Tendsto rate atTop (𝓝 r)) :
    Tendsto (fun n : ℕ => realPoissonProbability (rate n))
      atTop (𝓝 (realPoissonProbability r)) := by sorry
end
end Kyprianou.ProofPreparation
