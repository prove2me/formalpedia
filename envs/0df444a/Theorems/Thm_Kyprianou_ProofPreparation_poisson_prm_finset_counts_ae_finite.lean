-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_finset_counts_ae_finite
-- name    : Kyprianou.ProofPreparation.poisson_prm_finset_counts_ae_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:20:33.92821+00:00
-- url     : https://prove2.me/theorems/472989a7-6de2-4178-8269-2e45f70a46bf
-- title:
--   Simultaneous almost-sure finiteness of a finite family of Poisson region counts
-- statement:
--   For every finite family of measurable finite-intensity regions, all the corresponding Poisson random-measure counts are simultaneously finite almost surely. Uses the established single-region a.e. finiteness law and finite-event intersection. This is the bridge to samplewise integrability and equality of finite Poisson simple-function integrals.
-- source:
--   Kyprianou (2006), Chapter 2 Theorem 2.7, finite simple-function preliminary.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_finset_counts_ae_finite
    {Ω E ι : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (F : Finset ι) (A : ι → Set E)
    (hA : ∀ i ∈ F, MeasurableSet (A i))
    (hfin : ∀ i ∈ F, m (A i) < ⊤) :
    ∀ᵐ ω ∂P, ∀ i ∈ F,
      ProbabilityTheory.poissonRandomMeasure K Y ω (A i) < ⊤ := by sorry
end Kyprianou.ProofPreparation
