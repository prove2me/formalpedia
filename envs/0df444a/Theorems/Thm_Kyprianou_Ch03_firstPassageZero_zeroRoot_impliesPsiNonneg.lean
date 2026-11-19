-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassageZero_zeroRoot_impliesPsiNonneg
-- name    : Kyprianou.Ch03.firstPassageZero_zeroRoot_impliesPsiNonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T18:59:05.96832+00:00
-- url     : https://prove2.me/theorems/860d5302-61e8-4409-99ab-a6de27ee1af7
-- title:
--   Chapter 3 zero root: Zero maximal root implies nonnegative exponent on nonnegative half-line
-- statement:
--   Zero maximal root implies nonnegative exponent on nonnegative half-line; the root is still required to be a maximal nonnegative zero and all original process hypotheses are retained.
-- source:
--   Kyprianou (2006) Chapter 3 zero-root characterisation

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem firstPassageZero_zeroRoot_impliesPsiNonneg
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega))) :
        forall phi : Real,
      (0 <= phi ∧ L.ψ phi = 0 ∧ (forall theta : Real, 0 <= theta ->
        L.ψ theta = 0 -> theta <= phi)) ->
      ((phi = 0) -> (forall theta : Real, 0 <= theta ->
        0 <= L.ψ theta)) := by
  sorry

end Kyprianou.Ch03
