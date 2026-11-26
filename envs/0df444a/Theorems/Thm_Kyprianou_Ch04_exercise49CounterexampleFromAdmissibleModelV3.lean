-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49CounterexampleFromAdmissibleModelV3
-- name    : Kyprianou.Ch04.exercise49CounterexampleFromAdmissibleModelV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:53:00.816438+00:00
-- url     : https://prove2.me/theorems/521913c5-65a7-515c-88ba-52306f994554
-- title:
--   The original Exercise 4.9(iii) certificate is false whenever an admissible model exists
-- statement:
--   The original Exercise 4.9(iii) certificate is false whenever an admissible model exists
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), exceptional-path statement audit.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9Certification
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49CounterexampleFromAdmissibleModelV3
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hLevy : IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : ∀ (t : NNReal) (theta : ℝ),
      charFun (P.map (X t)) theta =
        Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent triplet theta))
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ y in Ioo (-1 : ℝ) 1, ENNReal.ofReal |y| ∂triplet.levyMeasure) < ⊤)
    (drift : ℝ)
    (hDrift : drift = triplet.drift - ∫ y in Ioo (-1 : ℝ) 1, y ∂triplet.levyMeasure)
    (hd : 0 < drift)
    (hNotSub : ¬ (∀ᵐ w ∂P, Monotone (fun t : NNReal => X t w)))
    (hInfinity : ∀ᵐ w ∂P, Tendsto (fun t : NNReal => X t w) atTop atTop) :
    ¬ certificate_ex4_9_iii := by
  sorry
