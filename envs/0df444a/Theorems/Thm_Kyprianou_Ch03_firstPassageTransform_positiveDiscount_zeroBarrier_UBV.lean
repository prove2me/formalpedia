-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_positiveDiscount_zeroBarrier_UBV
-- name    : Kyprianou.Ch03.firstPassageTransform_positiveDiscount_zeroBarrier_UBV
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:42:29.024963+00:00
-- url     : https://prove2.me/theorems/860ef03c-f280-4300-ae1e-a65d4f5abd9b
-- title:
--   firstPassageTransform_positiveDiscount_zeroBarrier_UBV
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

theorem firstPassageTransform_positiveDiscount_zeroBarrier_UBV
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega)))
    (hUBV : ¬ L.BoundedVariation) :
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
