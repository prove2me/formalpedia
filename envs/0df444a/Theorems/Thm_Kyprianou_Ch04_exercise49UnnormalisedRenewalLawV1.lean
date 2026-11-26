-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49UnnormalisedRenewalLawV1
-- name    : Kyprianou.Ch04.exercise49UnnormalisedRenewalLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:42:47.801455+00:00
-- url     : https://prove2.me/theorems/c2a89ccb-f832-508a-8137-94c2e9a41db7
-- title:
--   Physical renewal equation with the unnormalised first-deficit subprobability law
-- statement:
--   Physical renewal equation with the unnormalised first-deficit subprobability law
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49UnnormalisedRenewalLawV1
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
        0 < rho → rho < 1 →
        ∀ (finiteTime : Omega → NNReal),
          Measurable finiteTime →
          (∀ᵐ omega : Omega ∂P, tau 0 omega ≠ ⊤ →
            tau 0 omega = (finiteTime omega : WithTop NNReal)) →
          ∃ nu mu : Measure Real,
            nu Set.univ = ENNReal.ofReal rho ∧
            IsProbabilityMeasure mu ∧
            (∀ B : Set Real, MeasurableSet B →
              nu B = P {omega : Omega | tau 0 omega ≠ ⊤ ∧
                -(X (finiteTime omega) omega) ∈ B}) ∧
            (∀ x : Real, 0 ≤ x →
              (P {omega : Omega | tau x omega = ⊤}).toReal =
                (mu (Set.Iic x)).toReal) ∧
            mu = ENNReal.ofReal (1 - rho) • Measure.dirac 0 + mu.conv nu := by
  sorry
