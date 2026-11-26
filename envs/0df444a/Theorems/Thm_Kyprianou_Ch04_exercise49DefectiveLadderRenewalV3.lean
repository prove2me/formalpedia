-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49DefectiveLadderRenewalV3
-- name    : Kyprianou.Ch04.exercise49DefectiveLadderRenewalV3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T12:36:52.511729+00:00
-- url     : https://prove2.me/theorems/a90d064c-e6d8-471e-b5a8-de77259130d0
-- title:
--   Conditional deficit law and defective renewal formula
-- statement:
--   Under the exact original hypotheses, the strict probability bounds and any a.e.-correct measurable finite clock imply the conditional deficit law and geometric convolution survival identity.
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49DefectiveLadderRenewalV3
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
          ∃ eta : Measure Real,
            IsProbabilityMeasure eta ∧
            (∀ B : Set Real, MeasurableSet B →
              (eta B).toReal =
                (P {omega : Omega | tau 0 omega ≠ ⊤ ∧
                    -(X (finiteTime omega) omega) ∈ B}).toReal / rho) ∧
            let convPow : Nat -> Measure Real :=
              Nat.rec (Measure.dirac (0 : Real))
                (fun _ mu => mu.conv eta)
            ∀ x : Real, 0 ≤ x →
              (P {omega : Omega | tau x omega = ⊤}).toReal =
                (1 - rho) *
                  ∑' k : Nat, rho ^ k * (convPow k (Set.Iic x)).toReal := by
  sorry
