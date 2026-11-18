-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_two_cell_weighted_sq_integrable
-- name    : Kyprianou.ProofPreparation.poisson_prm_two_cell_weighted_sq_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:14:58.357663+00:00
-- url     : https://prove2.me/theorems/2a11d200-4e89-499c-83a6-ff4cbc518574
-- title:
--   Square integrability of weighted disjoint finite Poisson region counts
-- statement:
--   The weighted sum of two disjoint finite-intensity Poisson random-measure region counts has an integrable square under arbitrary real coefficients. Follows from public single-cell count square-integrability and first moments plus independent-count product integrability. Supports exact two-cell second-moment and L² approximation.
-- source:
--   Kyprianou (2006), Chapter 2 Theorem 2.7, finite simple Poisson stochastic integral square integrability.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_sq_integrable
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_real_first_moment
import Theorems.Thm_ProbabilityTheory_indepFun_poissonRandomMeasure_apply
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_two_cell_weighted_sq_integrable
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : m A < ⊤) (hfinB : m B < ⊤)
    (hAB : Disjoint A B) (a b : ℝ) :
    Integrable (fun ω =>
      (a * (ProbabilityTheory.poissonRandomMeasure K Y ω A).toReal +
       b * (ProbabilityTheory.poissonRandomMeasure K Y ω B).toReal) ^ 2) P := by sorry
end Kyprianou.ProofPreparation
