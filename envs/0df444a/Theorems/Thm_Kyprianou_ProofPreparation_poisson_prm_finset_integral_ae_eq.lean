-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_finset_integral_ae_eq
-- name    : Kyprianou.ProofPreparation.poisson_prm_finset_integral_ae_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:21:22.788628+00:00
-- url     : https://prove2.me/theorems/e69da121-7c47-45f8-9bd8-407624134800
-- title:
--   Almost-sure equality of a finite simple Poisson stochastic integral and weighted region counts
-- statement:
--   For an arbitrary finite family of measurable finite-intensity Poisson regions with arbitrary real weights, the original random-measure Bochner integral of the finite weighted indicator sum equals the corresponding finite weighted sum of real counts almost surely. Sample integrability is established by simultaneous a.e. finite counts, with no disjointness required. This generalises the two-cell stage of Kyprianou Chapter 2 Theorem 2.7.
-- source:
--   Kyprianou (2006) Chapter 2 Theorem 2.7, finite simple-function pathwise Poisson integration.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_finset_integral_ae_eq
    {Ω E ι : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [DecidableEq ι] [Nonempty E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (F : Finset ι) (A : ι → Set E) (a : ι → ℝ)
    (hA : ∀ i ∈ F, MeasurableSet (A i))
    (hfin : ∀ i ∈ F, m (A i) < ⊤) :
    ∀ᵐ ω ∂P,
      (∫ x, (∑ i ∈ F, a i * (A i).indicator (fun _ => (1 : ℝ)) x) ∂
        (ProbabilityTheory.poissonRandomMeasure K Y ω)) =
      ∑ i ∈ F, a i *
        (ProbabilityTheory.poissonRandomMeasure K Y ω (A i)).toReal := by sorry
end Kyprianou.ProofPreparation
