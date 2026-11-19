-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassageZero_consequence2
-- name    : Kyprianou.Ch03.firstPassageZero_consequence2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T15:03:25.710265+00:00
-- url     : https://prove2.me/theorems/cc2866e2-2907-4907-9827-36eccd6d6ac1
-- title:
--   Corollary 3.13 root/exact clause 2
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

theorem firstPassageZero_consequence2
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega))) :
        forall phi : Real,
      (0 <= phi ∧ L.ψ phi = 0 ∧ (forall theta : Real, 0 <= theta ->
        L.ψ theta = 0 -> theta <= phi)) ->
      (forall x : Real, 0 < x ->
        ((P {omega : Omega |
          firstHittingTime L.X (Set.Ioi x) omega != ⊤}).toReal = 1
          <-> phi = 0)) := by
  sorry

end Kyprianou.Ch03
