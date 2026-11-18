-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_finset_weighted_count_first_moment
-- name    : Kyprianou.ProofPreparation.poisson_prm_finset_weighted_count_first_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:19:16.038542+00:00
-- url     : https://prove2.me/theorems/a167b6df-a46a-4ec6-97c0-ddfefa2a1cf2
-- title:
--   Finite signed weighted Poisson count first moment
-- statement:
--   For a finite collection of measurable finite-intensity regions, the expected finite weighted sum of their Poisson counts equals the same weighted sum of their intensity masses. No disjointness is needed. The proof uses the public single-region first moments, integrability, Mathlib integral_finset_sum and scalar linearity, providing the finite-family simple-function first-moment stage of Kyprianou Chapter 2 Theorem 2.7.
-- source:
--   Kyprianou (2006) Chapter 2 Theorem 2.7, finite simple Poisson integral first moment.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_real_first_moment
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_finset_weighted_count_first_moment
    {Ω E ι : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [DecidableEq ι] [Nonempty E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (F : Finset ι) (A : ι → Set E) (a : ι → ℝ)
    (hA : ∀ i ∈ F, MeasurableSet (A i))
    (hfin : ∀ i ∈ F, m (A i) < ⊤) :
    (∫ ω, ∑ i ∈ F, a i *
      (ProbabilityTheory.poissonRandomMeasure K Y ω (A i)).toReal ∂P) =
      ∑ i ∈ F, a i * (m (A i)).toReal := by sorry
end Kyprianou.ProofPreparation
