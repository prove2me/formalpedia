-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_two_cell_second_moment
-- name    : Kyprianou.ProofPreparation.poisson_prm_two_cell_second_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:07:33.782671+00:00
-- url     : https://prove2.me/theorems/ce6d6c34-f3a7-4e89-9e30-539ae4205870
-- title:
--   Exact second moment of a weighted two-cell Poisson count integral
-- statement:
--   For two disjoint finite-intensity measurable cells and arbitrary real weights a,b, the true Poisson counts have exact weighted-sum squared mean equal to squared intensity mean plus weighted intensity variance. Uses only public Chapter 2 Poisson first/second moments and disjoint independence, preparing source-faithful finite simple-function approximation.
-- source:
--   Kyprianou (2006), Chapter 2 Theorem 2.7, two-cell simple Poisson integral second-moment calculation.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_sq_integrable
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_indicator_integral_second_moment
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_disjoint_cross_moment
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_real_first_moment
import Theorems.Thm_ProbabilityTheory_indepFun_poissonRandomMeasure_apply
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_two_cell_second_moment
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : m A < ⊤) (hfinB : m B < ⊤)
    (hAB : Disjoint A B) (a b : ℝ) :
    (∫ ω, (a * (ProbabilityTheory.poissonRandomMeasure K Y ω A).toReal +
      b * (ProbabilityTheory.poissonRandomMeasure K Y ω B).toReal) ^ 2 ∂P) =
      (a * (m A).toReal + b * (m B).toReal) ^ 2 +
        a ^ 2 * (m A).toReal + b ^ 2 * (m B).toReal := by sorry
end Kyprianou.ProofPreparation
