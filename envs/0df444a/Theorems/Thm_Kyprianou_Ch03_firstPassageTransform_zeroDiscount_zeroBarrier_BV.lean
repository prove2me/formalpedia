-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_zeroDiscount_zeroBarrier_BV
-- name    : Kyprianou.Ch03.firstPassageTransform_zeroDiscount_zeroBarrier_BV
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T07:49:34.545661+00:00
-- url     : https://prove2.me/theorems/c92bde07-f270-45d5-91a8-3a0bec7479a0
-- title:
--   firstPassageTransform_zeroDiscount_zeroBarrier_BV
-- statement:
--   Source-exact zero-discount first-passage formula at barrier zero in the bounded or unbounded variation case; all source hypotheses are retained.
-- source:
--   Kyprianou Chapter 3 upward first passage

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem firstPassageTransform_zeroDiscount_zeroBarrier_BV
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega)))
    (hBV : L.BoundedVariation) :
    forall (q : Real), q = 0 ->
          forall phi : Real,
      (0 <= phi ∧ L.ψ phi = q ∧ (forall theta : Real, 0 <= theta ->
          L.ψ theta = q -> theta <= phi)) ->
      (forall (x : Real), x = 0 ->
          forall (finiteTime : Omega -> NNReal),
            (forall omega,
              firstHittingTime L.X (Set.Ioi x) omega != ⊤ ->
                firstHittingTime L.X (Set.Ioi x) omega =
                  (finiteTime omega : WithTop NNReal)) ->
            (∫ omega,
              if firstHittingTime L.X (Set.Ioi x) omega = ⊤
              then (0 : Real)
              else Real.exp (-q * (finiteTime omega : Real)) ∂P) =
              Real.exp (-phi * x)) := by
  sorry

end Kyprianou.Ch03
