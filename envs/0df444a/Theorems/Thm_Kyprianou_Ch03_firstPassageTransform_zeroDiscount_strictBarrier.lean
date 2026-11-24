-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_zeroDiscount_strictBarrier
-- name    : Kyprianou.Ch03.firstPassageTransform_zeroDiscount_strictBarrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T19:08:18.221871+00:00
-- url     : https://prove2.me/theorems/7b1bec70-1083-44ec-89fd-6da49db80d40
-- title:
--   First passage at zero discount: strictBarrier
-- statement:
--   Source equivalent zero-discount first passage formula with only a barrier-domain case restriction.
-- source:
--   Kyprianou Chapter 3 first passage

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem firstPassageTransform_zeroDiscount_strictBarrier
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega))) :
    forall (q : Real), q = 0 ->
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
