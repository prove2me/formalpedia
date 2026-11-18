-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_disjoint_cross_moment
-- name    : Kyprianou.ProofPreparation.poisson_prm_disjoint_cross_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T11:25:58.996049+00:00
-- url     : https://prove2.me/theorems/68ce37b3-e7c0-4b78-afaa-ffc7b679b998
-- title:
--   Factorisation of disjoint Poisson count cross moments
-- statement:
--   Counts of two disjoint measurable finite-intensity regions of a Poisson random measure are independent and have joint real product mean equal to the product of their intensity masses, by exact evaluation independence and public Chapter 2 Campbell first moments. Off-diagonal term for the simple-function second-moment proof.
-- source:
--   Kyprianou (2006), Chapter 2 Theorem 2.7, disjoint simple-integral off-diagonal term.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_indepFun_poissonRandomMeasure_apply
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_real_first_moment
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_disjoint_cross_moment
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : m A < ⊤) (hfinB : m B < ⊤)
    (hAB : Disjoint A B) :
    (∫ ω, (ProbabilityTheory.poissonRandomMeasure K Y ω A).toReal *
      (ProbabilityTheory.poissonRandomMeasure K Y ω B).toReal ∂P) =
      (m A).toReal * (m B).toReal := by sorry
end Kyprianou.ProofPreparation
