-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_weighted_indicator_charfun
-- name    : Kyprianou.ProofPreparation.poisson_prm_weighted_indicator_charfun
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T11:28:20.671086+00:00
-- url     : https://prove2.me/theorems/283249b4-c9d7-4351-982c-b53141b3ab82
-- title:
--   Characteristic exponent of a weighted Poisson indicator integral
-- statement:
--   For a finite-intensity measurable region and any real weight a, the characteristic function of the actual Bochner Poisson integral of a times its indicator has the compound-Poisson exponent λ(exp(i aξ)−1). This gives the weighted one-cell building block for finite simple-function approximation in Kyprianou (2006) Chapter 2 Theorem 2.7.
-- source:
--   Kyprianou (2006) Chapter 2 Theorem 2.7, weighted simple integrand characteristic function.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_charFun_natCast_poissonRandomMeasure_apply
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_weighted_indicator_charfun
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A : Set E) (hA : MeasurableSet A) (hfin : m A < ⊤)
    (a ξ : ℝ) :
    charFun (P.map (fun ω => ∫ x, a * A.indicator (fun _ => (1 : ℝ)) x ∂
      (ProbabilityTheory.poissonRandomMeasure K Y ω))) ξ =
      Complex.exp (((m A).toReal : ℂ) *
        (Complex.exp ((((a * ξ : ℝ) : ℂ)) * Complex.I) - 1)) := by sorry
end Kyprianou.ProofPreparation
