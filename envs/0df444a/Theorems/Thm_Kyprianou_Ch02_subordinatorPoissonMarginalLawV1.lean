-- Prove2me | Theorems.Thm_Kyprianou_Ch02_subordinatorPoissonMarginalLawV1
-- name    : Kyprianou.Ch02.subordinatorPoissonMarginalLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:40:58.213074+00:00
-- url     : https://prove2.me/theorems/63312c1e-8456-45ee-aca3-4f500cf50f12
-- title:
--   Positive finite-variation jump intensity has a nonnegative shifted Poisson marginal law
-- statement:
--   Construct a Poisson point family with intensity t times the positive restriction of ν. Integrate the nonnegative mark function max(x,0), whose truncated first moment is finite. Apply the proved Poisson random measure integral laws and measurable nonnegative integral theorem. Shift its distribution by t*d and use the characteristic function translation rule.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14; sufficiency of the subordinator criterion.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.subordinatorPoissonMarginalLawV1
    (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    (hint : Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (ν.restrict (Set.Ioi (0 : ℝ)))) (t : ℝ≥0)
    (d : ℝ) (hd : 0 ≤ d) :
    ∃ Q : Measure ℝ, IsProbabilityMeasure Q ∧ Q (Set.Iio (0 : ℝ)) = 0 ∧
      ∀ ξ : ℝ, charFun Q ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          (Complex.I * ((d * ξ : ℝ) : ℂ) +
            ∫ x in Set.Ioi (0 : ℝ),
              (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν)) := by
  sorry
