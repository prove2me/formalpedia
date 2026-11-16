-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise59ZeroDriftPolarPoints
-- name    : Kyprianou.Ch05.exercise59ZeroDriftPolarPoints
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:59:44.093189+00:00
-- url     : https://prove2.me/theorems/0d888e43-3c65-454e-81b8-2997938b210a
-- title:
--   Exercise 5.9: point polarity for zero-drift infinite-activity BV Lévy processes
-- statement:
--   For any bounded-variation Lévy process whose finite-variation compensated drift is zero and whose Lévy measure is infinite, every fixed point is polar at strictly positive times; additionally construct two independent nonnegative subordinators on the same probability space whose difference equals the original process almost surely at all times. The no-hitting claim is preserved for all x in R, including zero.
-- source:
--   Kyprianou (2006), first edition, Exercise 5.9 printed p.138, worked solution pp.329-330.

import Mathlib
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Exercise 5.9: zero-drift bounded variation, infinite-activity
non-compound-Poisson Levy paths do not hit any prescribed point
at any strictly positive time; a decomposition into independent
subordinators is simultaneously supplied. -/
theorem exercise59ZeroDriftPolarPoints
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : ∀ (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (hBV : triplet.gaussianVariance = 0 ∧
       (∫⁻ z in Set.Ioo (-1 : Real) 1,
         ENNReal.ofReal |z| ∂triplet.levyMeasure) < ⊤)
    (hZeroDrift : triplet.drift -
       (∫ z in Set.Ioo (-1 : Real) 1, z ∂triplet.levyMeasure) = 0)
    (hNotCompoundPoisson : triplet.levyMeasure Set.univ = ⊤) :
  (∀ x : Real,
    P {omega : Omega |
      ∃ t : NNReal, 0 < t ∧ X t omega = x} = 0) ∧
  ∃ Xplus Xminus : NNReal → Omega → Real,
    Kyprianou.Ch03.IsSubordinator P Xplus ∧
    Kyprianou.Ch03.IsSubordinator P Xminus ∧
    (∀ᵐ omega : Omega ∂P, ∀ t : NNReal,
       X t omega = Xplus t omega - Xminus t omega) ∧
    Indep
      (MeasurableSpace.comap
        (fun omega : Omega => fun t : NNReal => Xplus t omega) inferInstance)
      (MeasurableSpace.comap
        (fun omega : Omega => fun t : NNReal => Xminus t omega) inferInstance)
      P
 := by
  sorry

end Kyprianou.Ch05
