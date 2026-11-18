-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_two_cell_charfun
-- name    : Kyprianou.ProofPreparation.poisson_prm_two_cell_charfun
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T11:30:42.039954+00:00
-- url     : https://prove2.me/theorems/09f88d07-2228-4656-b3f7-164255610936
-- title:
--   Characteristic exponent of two weighted disjoint Poisson region counts
-- statement:
--   The characteristic function of a weighted sum of counts in two disjoint finite-intensity Poisson regions equals the exponential of the sum of their compound-Poisson exponents. Derived from proved independence, the exact Poisson region count characteristic functions and Mathlib’s additivity under independence, giving the two-cell source precursor to Chapter 2 Theorem 2.7.
-- source:
--   Kyprianou (2006) Chapter 2 Theorem 2.7, finite simple-function characteristic exponent.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_indepFun_poissonRandomMeasure_apply
import Theorems.Thm_ProbabilityTheory_charFun_natCast_poissonRandomMeasure_apply
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_two_cell_charfun
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : m A < ⊤) (hfinB : m B < ⊤)
    (hAB : Disjoint A B) (a b ξ : ℝ) :
    charFun (P.map (fun ω =>
      a * (ProbabilityTheory.poissonRandomMeasure K Y ω A).toReal +
      b * (ProbabilityTheory.poissonRandomMeasure K Y ω B).toReal)) ξ =
      Complex.exp ((((m A).toReal : ℂ) *
        (Complex.exp ((((a * ξ : ℝ) : ℂ)) * Complex.I) - 1)) +
        (((m B).toReal : ℂ) *
        (Complex.exp ((((b * ξ : ℝ) : ℂ)) * Complex.I) - 1))) := by sorry
end Kyprianou.ProofPreparation
