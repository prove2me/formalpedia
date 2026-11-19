-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_consequence1
-- name    : Kyprianou.Ch03.firstPassageTransform_consequence1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T15:03:25.929581+00:00
-- url     : https://prove2.me/theorems/b64a0afd-0aaf-4604-9c18-b000fc8f2781
-- title:
--   Theorem 3.12 root/exact clause 1
-- statement:
--   Necessary and sufficient proof obligation in a sound source-preserving reduction of Theorem 3.12. Retains the original process hypotheses and the same maximal nonnegative Laplace-exponent root.
-- source:
--   Kyprianou (2006), first edition, Chapter 3, Theorem 3.12

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem firstPassageTransform_consequence1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega))) :
    forall (q : Real), 0 <= q ->
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
