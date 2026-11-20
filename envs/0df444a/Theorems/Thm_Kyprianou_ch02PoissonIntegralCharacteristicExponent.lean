-- Prove2me | Theorems.Thm_Kyprianou_ch02PoissonIntegralCharacteristicExponent
-- name    : Kyprianou.ch02PoissonIntegralCharacteristicExponent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:44:06.500308+00:00
-- url     : https://prove2.me/theorems/3102ab48-a9b8-46f0-b556-637f92adf0b0
-- title:
--   Characteristic exponent of a Poisson integral
-- statement:
--   Characteristic exponent of a Poisson integral. Proper source-exact component of Kyprianou Chapter 2 Theorem 2.7, with original quantification and hypotheses.
-- source:
--   Kyprianou (2006) Chapter 2 Theorem 2.7

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou
theorem ch02PoissonIntegralCharacteristicExponent
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (f : E → ℝ) (hf : Measurable f) :
(Integrable (fun x => min (1 : ℝ) |f x|) m →
      ∀ ξ : ℝ,
        charFun (P.map (fun ω =>
          ∫ x, f x ∂(ProbabilityTheory.poissonRandomMeasure K Y ω))) ξ =
        Complex.exp
          (∫ x, (Complex.exp (Complex.I *
            (((ξ * f x : ℝ) : ℂ))) - 1) ∂m))    := by sorry
end Kyprianou
