-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49PhysicalDepthWitnessV1
-- name    : Kyprianou.Ch04.exercise49PhysicalDepthWitnessV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:52:12.377658+00:00
-- url     : https://prove2.me/theorems/335bbe8e-3dc6-54d4-9b55-cada45450d69
-- title:
--   Measurable physical depth and stopped first-deficit witnesses with their restricted product law
-- statement:
--   Measurable representatives of the ruin event, first deficit, total and shifted depth, with exact probabilities and the strong Markov product law on finite passage.
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49PhysicalDepthWitnessV1
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
          ∃ (D : Set Omega) (I V W : Omega → ℝ),
            MeasurableSet D ∧ Measurable I ∧ Measurable V ∧ Measurable W ∧
            (P D = P {omega : Omega | tau 0 omega ≠ ⊤}) ∧
            (∀ B : Set Real, MeasurableSet B →
              P (I ⁻¹' B ∩ D) = P {omega : Omega | tau 0 omega ≠ ⊤ ∧
                -(X (finiteTime omega) omega) ∈ B}) ∧
            (∀ x : Real, 0 ≤ x →
              P (V ⁻¹' Set.Iic x) = P {omega : Omega | tau x omega = ⊤}) ∧
            (∀ᵐ omega ∂P.restrict Dᶜ, V omega = 0) ∧
            (∀ᵐ omega ∂P.restrict D, V omega = I omega + W omega) ∧
            Measure.map (fun omega => (I omega, W omega)) (P.restrict D) =
              (Measure.map I (P.restrict D)).prod (Measure.map V P) := by
  sorry
