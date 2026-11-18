-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_two_cell_integral_ae_eq
-- name    : Kyprianou.ProofPreparation.poisson_prm_two_cell_integral_ae_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T11:22:33.365271+00:00
-- url     : https://prove2.me/theorems/0c3b8611-8e7d-47b6-958e-60f2d6460926
-- title:
--   A.e. identity between a two-cell Poisson integral and weighted region counts
-- statement:
--   For two finite-intensity measurable cells A,B and any real weights a,b, the Bochner integral of a linear combination of their indicators against the original Poisson random measure agrees almost surely with the corresponding weighted real region counts. This is the exact bridge from Poisson count moment identities to the stochastic integral in Kyprianou (2006), Chapter 2 Theorem 2.7; disjointness is not necessary for this linear identity.
-- source:
--   Kyprianou (2006), Chapter 2 Theorem 2.7, finite simple integrand identification.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_two_cell_integral_ae_eq
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : m A < ⊤) (hfinB : m B < ⊤)
    (a b : ℝ) :
    ∀ᵐ ω ∂P,
      (∫ x, (a * A.indicator (fun _ => (1 : ℝ)) x +
        b * B.indicator (fun _ => (1 : ℝ)) x) ∂
        (ProbabilityTheory.poissonRandomMeasure K Y ω)) =
          a * (ProbabilityTheory.poissonRandomMeasure K Y ω A).toReal +
            b * (ProbabilityTheory.poissonRandomMeasure K Y ω B).toReal := by sorry
end Kyprianou.ProofPreparation
