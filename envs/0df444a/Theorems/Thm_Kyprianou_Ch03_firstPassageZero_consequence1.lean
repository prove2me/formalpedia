-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassageZero_consequence1
-- name    : Kyprianou.Ch03.firstPassageZero_consequence1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T15:03:17.777594+00:00
-- url     : https://prove2.me/theorems/4e91de62-2135-46df-b67b-af66d739802f
-- title:
--   Corollary 3.13 root/exact clause 1
-- statement:
--   Necessary and sufficient proof obligation in a sound source-preserving reduction of Corollary 3.13. Retains the original process hypotheses and the same maximal nonnegative Laplace-exponent root.
-- source:
--   Kyprianou (2006), first edition, Chapter 3, Corollary 3.13

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem firstPassageZero_consequence1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega))) :
        forall phi : Real,
      (0 <= phi ∧ L.ψ phi = 0 ∧ (forall theta : Real, 0 <= theta ->
        L.ψ theta = 0 -> theta <= phi)) ->
      (forall x : Real, 0 <= x ->
        forall finiteTime : Omega -> NNReal,
          (forall omega,
            firstHittingTime L.X (Set.Ioi x) omega != ⊤ ->
              firstHittingTime L.X (Set.Ioi x) omega =
                (finiteTime omega : WithTop NNReal)) ->
          (P {omega : Omega |
            firstHittingTime L.X (Set.Ioi x) omega != ⊤}).toReal =
              Real.exp (-phi * x)) := by
  sorry

end Kyprianou.Ch03
