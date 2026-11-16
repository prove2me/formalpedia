-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise53SizeBiasedUniformRepresentation
-- name    : Kyprianou.Ch05.exercise53SizeBiasedUniformRepresentation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:56:54.932598+00:00
-- url     : https://prove2.me/theorems/54a147ee-9cbb-49b4-84c3-f54840d7fc01
-- title:
--   Exercise 5.3: independent-uniform size-biased jump representation
-- statement:
--   If (V,W) is the limiting joint overshoot/undershoot distribution, Z the limiting jump size, and Uuniform an independent [0,1]-uniform variable, establish the entire joint distributional identity (V,W) =_law ((1-Uuniform)*Z,Uuniform*Z). Weak-limit hypotheses define V,W,Z via bounded continuous test functions; Uuniform is independent of all three, not merely marginally uniform.
-- source:
--   Kyprianou (2006), first edition, Exercise 5.3 printed p.134, worked solution printed p.323.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Exercise 5.3: the entire joint distributional size-biased-uniform
representation (V,W) =_d ((1-U)Z,UZ), with independent Uniform(0,1) U. -/
theorem exercise53SizeBiasedUniformRepresentation
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (hMean : Integrable (Y (1 : NNReal)) P)
    (hPositiveMean : 0 < ∫ omega, Y 1 omega ∂P)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hNonLattice : NonLatticeMeasure (U 0))
    (V W Z Uunif : Omega → Real)
    (hMeasurableV : Measurable V)
    (hMeasurableW : Measurable W)
    (hMeasurableZ : Measurable Z)
    (hMeasurableU : Measurable Uunif)
    (hLimitPair : ∀ f : Real × Real → Real,
       IsBoundedContinuousTest f →
         Tendsto
           (fun x : Real => passageTestExpectation P Y Yleft death x f)
           atTop (nhds (∫ omega, f (V omega,W omega) ∂P)))
    (hLimitJump : ∀ g : Real → Real, Continuous g →
       (∃ M : Real, 0 ≤ M ∧ ∀ z : Real, |g z| ≤ M) →
         Tendsto
           (fun x : Real =>
             passageTestExpectation P Y Yleft death x
               (fun pair : Real × Real => g (pair.1+pair.2)))
           atTop (nhds (∫ omega, g (Z omega) ∂P)))
    (hUniform : Measure.map Uunif P =
       (volume : Measure Real).restrict (Set.Icc (0 : Real) 1))
    (hIndependent : ∀ (A : Set Real) (B : Set (Real × Real × Real)),
       MeasurableSet A → MeasurableSet B →
         P {omega : Omega |
           Uunif omega ∈ A ∧
           (V omega,W omega,Z omega) ∈ B} =
         P {omega : Omega | Uunif omega ∈ A} *
         P {omega : Omega | (V omega,W omega,Z omega) ∈ B}) :
  Measure.map (fun omega : Omega => (V omega,W omega)) P =
    Measure.map
      (fun omega : Omega =>
        ((1-Uunif omega)*Z omega,Uunif omega*Z omega)) P
 := by
  sorry

end Kyprianou.Ch05
