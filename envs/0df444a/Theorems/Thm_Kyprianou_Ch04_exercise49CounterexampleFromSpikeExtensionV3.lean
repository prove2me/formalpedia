-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49CounterexampleFromSpikeExtensionV3
-- name    : Kyprianou.Ch04.exercise49CounterexampleFromSpikeExtensionV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:53:10.940799+00:00
-- url     : https://prove2.me/theorems/2cea6ad6-b883-445f-b465-01998bb17531
-- title:
--   Every admissible Levy model has a null extension contradicting the pointwise representative requirement
-- statement:
--   Every admissible Levy model has a null extension contradicting the pointwise representative requirement
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), exceptional-path statement audit.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9Certification
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49CounterexampleFromSpikeExtensionV3
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
    (hInfinity : ∀ᵐ w ∂P, Tendsto (fun t : NNReal => X t w) atTop atTop)
    {E : Type} [MeasurableSpace E] (a : E → NNReal)
    (ha : ∀ e, 0 < a e) (hBad : ¬ MeasurableSet {e | a e ≤ 1}) :
    ¬ certificate_ex4_9_iii := by
  sorry
