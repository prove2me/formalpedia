-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_large_count_ae_finite_of_integrable_truncated
-- name    : Kyprianou.ProofPreparation.poisson_prm_large_count_ae_finite_of_integrable_truncated
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T13:32:05.580909+00:00
-- url     : https://prove2.me/theorems/14d7191c-6765-4ce2-9c18-d1cdeecb4f70
-- title:
--   Almost-sure finite large-mark Poisson counts under truncated integrability
-- statement:
--   If ∫ min(1,|f|) dm is finite then the number of Poisson points with |f(mark)|>1 is finite almost surely. The large-mark region is measurable and has finite intensity by the proved truncated integrability lemma. Apply the source-proved finite-region Poisson count almost-sure finiteness. This is the large-jump finite-activity part of Kyprianou Chapter 2 Theorem 2.7 absolute convergence.
-- source:
--   Kyprianou (2006) Chapter 2 Theorem 2.7, finite large-mark count under ∫min(1,|f|)dm<∞.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_measure_large_values_lt_top_of_integrable_truncated
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_large_count_ae_finite_of_integrable_truncated
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (f : E → ℝ) (hf : Measurable f)
    (htrunc : Integrable (fun x => min (1 : ℝ) |f x|) m) :
    ∀ᵐ ω ∂P,
      ProbabilityTheory.poissonRandomMeasure K Y ω {x | 1 < |f x|} < ⊤ := by sorry
end Kyprianou.ProofPreparation
