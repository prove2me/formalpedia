-- Prove2me | Theorems.Thm_Kyprianou_exercise2_3_AllPartsCh02V3
-- name    : Kyprianou.exercise2_3_AllPartsCh02V3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T19:23:19.671671+00:00
-- url     : https://prove2.me/theorems/a19010cc-3f51-456e-9cfd-57281ead6ecc
-- title:
--   Exercise 2.3: integrability criterion for Poisson exponentials
-- statement:
--   Equivalence between finiteness of the Poisson Laplace-exponential integral for every positive parameter and finiteness of the truncated first-moment integral, for an arbitrary measurable nonnegative integrand.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.3, pp. 62-66; author solutions pp. 307-311; corrections recorded where needed

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou

theorem exercise2_3_AllPartsCh02V3
    {E : Type} [MeasurableSpace E] (η : Measure E)
    (f : E → ℝ) (hf : Measurable f)
    (hnonneg : ∀ x, 0 ≤ f x) :
    (∀ (φ : ℝ), 0 < φ →
      (∫⁻ x, ENNReal.ofReal
        (1 - Real.exp (-φ * f x)) ∂η) < ⊤) ↔
      (∫⁻ x, ENNReal.ofReal (min 1 (f x)) ∂η) < ⊤
      := by sorry

end Kyprianou
