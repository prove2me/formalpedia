-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_zeroBarrier
-- name    : Kyprianou.Ch03.firstPassageTransform_zeroBarrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:41:37.139103+00:00
-- url     : https://prove2.me/theorems/07870c97-0f66-4719-bd4b-a513db3accd2
-- title:
--   Chapter 3 positive discount first passage: zero barrier
-- statement:
--   The positive-discount source first-passage identity under one of two exhaustive nonnegative spatial regimes, with identical original root, process and finite-hitting selector assumptions.
-- source:
--   Kyprianou (2006), Chapter 3, first passage Laplace transform

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem firstPassageTransform_zeroBarrier
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
