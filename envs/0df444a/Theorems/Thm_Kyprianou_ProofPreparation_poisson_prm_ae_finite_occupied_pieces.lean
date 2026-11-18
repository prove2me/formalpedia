-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_ae_finite_occupied_pieces
-- name    : Kyprianou.ProofPreparation.poisson_prm_ae_finite_occupied_pieces
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T13:30:13.910809+00:00
-- url     : https://prove2.me/theorems/7bdacbcb-e2cf-48ca-aa90-4242c6de7f2f
-- title:
--   Only finitely many Poisson partition pieces contain points in a finite-intensity region
-- statement:
--   For any Poisson point family and measurable finite-intensity region S, almost surely only finitely many sigma-finite partition pieces contain at least one realised point in S. Derive from exact public Poisson random-measure nonnegative integral equals sum over realised points, the finite-region a.s. count law, and the pinned ENNReal finite_const_le_of_tsum_ne_top lemma. A source-backed generalisation of the finite band lemma in LeanLevy's PoissonMartingale and the large-mark step of Kyprianou Chapter 2 Theorem 2.7.
-- source:
--   Kyprianou (2006), Chapter 2 Theorem 2.7; LeanLevy RandomMeasure/PoissonMartingale.lean finite band occupied-pieces proof.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_lintegral_poissonRandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_ae_finite_occupied_pieces
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (S : Set E) (hS : MeasurableSet S) (hfin : m S < ⊤) :
    ∀ᵐ ω ∂P,
      Set.Finite {k : ℕ | ∃ n ∈ Finset.range (K k ω), Y k n ω ∈ S} := by sorry
end Kyprianou.ProofPreparation
