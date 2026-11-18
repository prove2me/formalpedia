-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_two_cell_integral_first_moment
-- name    : Kyprianou.ProofPreparation.poisson_prm_two_cell_integral_first_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:10:00.281204+00:00
-- url     : https://prove2.me/theorems/48716759-4c46-4758-b214-429c656ca844
-- title:
--   First moment of a two-cell real Poisson integral
-- statement:
--   For any two measurable sets with finite Poisson intensity and arbitrary real weights, the expectation of the original Poisson random-measure Bochner integral of the weighted indicator sum equals the corresponding weighted intensity sum; no disjointness is required. A direct extension of the Chapter 2 Campbell identity to signed two-cell simple functions.
-- source:
--   Kyprianou (2006), Chapter 2 Theorem 2.7, signed finite-simple first moment.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_two_cell_integral_ae_eq
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_real_first_moment
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_two_cell_integral_first_moment
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : m A < ⊤) (hfinB : m B < ⊤)
    (a b : ℝ) :
    (∫ ω, (∫ x, (a * A.indicator (fun _ => (1 : ℝ)) x +
      b * B.indicator (fun _ => (1 : ℝ)) x) ∂
      (ProbabilityTheory.poissonRandomMeasure K Y ω)) ∂P) =
      a * (m A).toReal + b * (m B).toReal := by sorry
end Kyprianou.ProofPreparation
