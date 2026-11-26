-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49RhoPositiveV3
-- name    : Kyprianou.Ch04.exercise49RhoPositiveV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:36:46.790592+00:00
-- url     : https://prove2.me/theorems/012ac218-0043-5204-bba1-388b5d8ead0c
-- title:
--   Strict positivity of eventual ruin probability
-- statement:
--   Under the original BV hypotheses, the non-subordinator has positive eventual downward passage probability.
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49RhoPositiveV3
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : ∀ (t : NNReal) (theta : Real),
      charFun (P.map (X t)) theta =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet theta))
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ y in Set.Ioo (-1 : Real) 1,
        ENNReal.ofReal |y| ∂triplet.levyMeasure) < ⊤)
    (drift : Real)
    (hDrift : drift = triplet.drift -
      ∫ y in Set.Ioo (-1 : Real) 1, y ∂triplet.levyMeasure)
    (hd : 0 < drift)
    (hNotSubordinator :
      ¬ (∀ᵐ omega : Omega ∂P, Monotone (fun t : NNReal => X t omega)))
    (hTendsInfinity : ∀ᵐ omega : Omega ∂P,
      Tendsto (fun t : NNReal => X t omega) atTop atTop) :
    let tau : Real -> Omega -> WithTop NNReal := fun initial omega =>
          sInf {v : WithTop NNReal |
            ∃ t : NNReal, v = ↑t ∧ 0 < t ∧
              initial + X t omega < 0}
        let rho : Real := (P {omega : Omega | tau 0 omega ≠ ⊤}).toReal
        0 < rho := by
  sorry
