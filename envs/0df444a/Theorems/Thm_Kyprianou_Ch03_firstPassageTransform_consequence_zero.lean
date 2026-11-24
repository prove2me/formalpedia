-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_consequence_zero
-- name    : Kyprianou.Ch03.firstPassageTransform_consequence_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:30:51.390037+00:00
-- url     : https://prove2.me/theorems/cb091a65-f201-404d-99ba-f6a16e7b28c8
-- title:
--   Chapter 3 first passage transform: zero discount
-- statement:
--   Exact original first-passage Laplace transform consequent, restricted to one disjoint regime of q>=0. The original maximal exponent root, hitting time and finite-time selector premises remain unchanged.
-- source:
--   Kyprianou (2006) Chapter 3 upward passage Laplace transform

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem firstPassageTransform_consequence_zero
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
      (forall (x : Real), 0 <= x ->
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
