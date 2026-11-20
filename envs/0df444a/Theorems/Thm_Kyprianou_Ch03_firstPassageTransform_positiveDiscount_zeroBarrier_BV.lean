-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_positiveDiscount_zeroBarrier_BV
-- name    : Kyprianou.Ch03.firstPassageTransform_positiveDiscount_zeroBarrier_BV
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T07:42:31.368363+00:00
-- url     : https://prove2.me/theorems/b5d91696-f8f7-4abc-81ae-3dd470a33948
-- title:
--   firstPassageTransform_positiveDiscount_zeroBarrier_BV
-- statement:
--   Exact positive-discount first-passage zero-barrier formula for the specified bounded/unbounded variation regime; all original hypotheses retained.
-- source:
--   Kyprianou (2006) Chapter 3 positive-discount first-passage

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem firstPassageTransform_positiveDiscount_zeroBarrier_BV
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega)))
    (hBV : L.BoundedVariation) :
    forall (q : Real), 0 < q ->
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
