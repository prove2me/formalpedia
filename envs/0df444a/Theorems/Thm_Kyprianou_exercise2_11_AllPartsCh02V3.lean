-- Prove2me | Theorems.Thm_Kyprianou_exercise2_11_AllPartsCh02V3
-- name    : Kyprianou.exercise2_11_AllPartsCh02V3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T19:25:25.270948+00:00
-- url     : https://prove2.me/theorems/f0293346-4bbe-440f-80d2-2a9543f78466
-- title:
--   Exercise 2.11: subordinator Laplace exponent, tail identity and drift recovery
-- statement:
--   All three assertions: the subordinator Laplace exponent has drift-plus-jumps form, the jump contribution equals q times the exponential transform of the Lévy tail, and dividing the exponent by q recovers drift as q tends to infinity.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.11, pp. 62-66; author solutions pp. 307-311; corrections recorded where needed

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou

theorem exercise2_11_AllPartsCh02V3
    (a : ℝ) (σ : ℝ≥0) (ν : Measure ℝ)
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hsub : ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 => X t ω))
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, ν, hν⟩ ξ)) :
    let d : ℝ := -a - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂ν
    (∀ q : ℝ, 0 ≤ q →
       ∫ ω, Real.exp (-q * X 1 ω) ∂P =
       Real.exp (-(d * q +
         ∫ x in Set.Ioi (0 : ℝ),
           (1 - Real.exp (-q * x)) ∂ν))) ∧
    (∀ q : ℝ, 0 < q →
       ∫ x in Set.Ioi (0 : ℝ),
          (1 - Real.exp (-q * x)) ∂ν =
       q * ∫ x in Set.Ioi (0 : ℝ),
          Real.exp (-q * x) * (ν (Set.Ioi x)).toReal ∂volume) ∧
    Tendsto (fun q : ℝ =>
       (d * q +
         ∫ x in Set.Ioi (0 : ℝ),
           (1 - Real.exp (-q * x)) ∂ν) / q)
       atTop (nhds d)
      := by sorry

end Kyprianou
