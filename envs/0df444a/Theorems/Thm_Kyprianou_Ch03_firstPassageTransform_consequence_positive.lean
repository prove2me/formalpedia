-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_consequence_positive
-- name    : Kyprianou.Ch03.firstPassageTransform_consequence_positive
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T17:30:52.740194+00:00
-- url     : https://prove2.me/theorems/a39c9529-bf0f-4c3f-a821-e47098076d3f
-- title:
--   Chapter 3 first passage transform: positive discount
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

theorem firstPassageTransform_consequence_positive
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
