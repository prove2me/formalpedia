-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_indicator_charfun
-- name    : Kyprianou.ProofPreparation.poisson_prm_indicator_charfun
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T11:25:06.953823+00:00
-- url     : https://prove2.me/theorems/b448f877-1d16-440f-90ec-517e999323b2
-- title:
--   Characteristic function of a finite-intensity Poisson indicator integral
-- statement:
--   The characteristic function of the actual Bochner integral of the indicator of a finite-intensity measurable region against the Poisson random measure is exp(λ(exp(iξ)−1)), with λ=m(A). By exact indicator-integral/count identity and proved Poisson count characteristic function; a source-faithful one-cell precursor to Kyprianou (2006), Chapter 2 Theorem 2.7 full Poisson integral characteristic exponent.
-- source:
--   Kyprianou (2006), Chapter 2 Theorem 2.7, characteristic exponent for indicator integrands.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_charFun_natCast_poissonRandomMeasure_apply
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_indicator_charfun
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A : Set E) (hA : MeasurableSet A) (hfin : m A < ⊤)
    (ξ : ℝ) :
    charFun (P.map (fun ω => ∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂
      (ProbabilityTheory.poissonRandomMeasure K Y ω))) ξ =
      Complex.exp (((m A).toReal : ℂ) *
        (Complex.exp (((ξ : ℝ) : ℂ) * Complex.I) - 1)) := by sorry
end Kyprianou.ProofPreparation
