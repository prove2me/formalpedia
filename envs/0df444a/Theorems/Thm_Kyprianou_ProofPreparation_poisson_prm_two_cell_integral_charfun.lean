-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_two_cell_integral_charfun
-- name    : Kyprianou.ProofPreparation.poisson_prm_two_cell_integral_charfun
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:12:21.523566+00:00
-- url     : https://prove2.me/theorems/6ab1d81c-85ed-41a1-b630-1c93e1fe2e45
-- title:
--   Exact Poisson characteristic exponent for a two-cell stochastic integral
-- statement:
--   The characteristic function of the actual Poisson stochastic integral of a real simple function supported on two disjoint finite-intensity measurable sets equals the compound-Poisson exponent obtained by integrating exp(iξ f)-1 over the two cells. Exact consequence of a.e. identity between integral and weighted count sum, and the proved two-cell count characteristic function.
-- source:
--   Kyprianou (2006) Chapter 2 Theorem 2.7, two-cell simple-function characteristic exponent.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_two_cell_integral_ae_eq
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_two_cell_charfun
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_two_cell_integral_charfun
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : m A < ⊤) (hfinB : m B < ⊤)
    (hAB : Disjoint A B) (a b ξ : ℝ) :
    charFun (P.map (fun ω =>
      ∫ x, (a * A.indicator (fun _ => (1 : ℝ)) x +
        b * B.indicator (fun _ => (1 : ℝ)) x) ∂
        (ProbabilityTheory.poissonRandomMeasure K Y ω))) ξ =
      Complex.exp ((((m A).toReal : ℂ) *
        (Complex.exp ((((a * ξ : ℝ) : ℂ)) * Complex.I) - 1)) +
        (((m B).toReal : ℂ) *
        (Complex.exp ((((b * ξ : ℝ) : ℂ)) * Complex.I) - 1))) := by sorry
end Kyprianou.ProofPreparation
