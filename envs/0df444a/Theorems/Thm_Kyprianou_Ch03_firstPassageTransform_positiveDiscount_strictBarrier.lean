-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_positiveDiscount_strictBarrier
-- name    : Kyprianou.Ch03.firstPassageTransform_positiveDiscount_strictBarrier
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T19:05:35.273623+00:00
-- url     : https://prove2.me/theorems/313b7f86-9e94-485e-8a3c-a725c49a2bcd
-- title:
--   Kyprianou.Ch03.firstPassageTransform_positiveDiscount_strictBarrier
-- statement:
--   The exact positive-discount first passage transform at the specified barrier case, with all original assumptions.
-- source:
--   Kyprianou Chapter 3 first passage

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem firstPassageTransform_positiveDiscount_strictBarrier
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega))) :
    forall (q : Real), 0 < q ->
          forall phi : Real,
      (0 <= phi ∧ L.ψ phi = q ∧ (forall theta : Real, 0 <= theta ->
          L.ψ theta = q -> theta <= phi)) ->
      (forall (x : Real), 0 < x ->
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
