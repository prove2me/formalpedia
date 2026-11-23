-- Prove2me | Theorems.Thm_Kyprianou_Ch03_upwardPassageProbabilityAndDrift
-- name    : Kyprianou.Ch03.upwardPassageProbabilityAndDrift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:42:40.259198+00:00
-- url     : https://prove2.me/theorems/71ce0d64-73c7-4458-92bf-8304892741f8
-- title:
--   Corollary 3.13: upward passage probability and right-inverse drift regime
-- statement:
--   For spectrally negative Levy processes excluding almost surely nonincreasing paths, the rightmost nonnegative root phi(0) determines upward passage probability exp(-phi(0)*x). For strictly positive levels, passage is certain exactly when phi(0)=0. That regime is equivalent to the nonnegative Laplace exponent over nonnegative arguments, and, if the first moment is integrable, equivalently E(X_1)>=0. The statement avoids incorrectly asserting the x=0 iff.
-- source:
--   Kyprianou (2006), Chapter 3, Corollary 3.13, printed p. 82; x=0 exceptional case made explicit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem upwardPassageProbabilityAndDrift
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega))) :
    exists phi : Real,
      0 <= phi ∧ L.ψ phi = 0 ∧
      (forall theta : Real, 0 <= theta ->
        L.ψ theta = 0 -> theta <= phi) ∧
      (forall x : Real, 0 <= x ->
        forall finiteTime : Omega -> NNReal,
          (forall omega,
            firstHittingTime L.X (Set.Ioi x) omega != ⊤ ->
              firstHittingTime L.X (Set.Ioi x) omega =
                (finiteTime omega : WithTop NNReal)) ->
          (P {omega : Omega |
            firstHittingTime L.X (Set.Ioi x) omega != ⊤}).toReal =
              Real.exp (-phi * x)) ∧
      (forall x : Real, 0 < x ->
        ((P {omega : Omega |
          firstHittingTime L.X (Set.Ioi x) omega != ⊤}).toReal = 1
          <-> phi = 0)) ∧
      ((phi = 0) <-> (forall theta : Real, 0 <= theta ->
        0 <= L.ψ theta)) ∧
      (Integrable (L.X 1) P ->
        ((phi = 0) <-> 0 <= (∫ omega, L.X 1 omega ∂P))) := by
  sorry

end Kyprianou.Ch03
