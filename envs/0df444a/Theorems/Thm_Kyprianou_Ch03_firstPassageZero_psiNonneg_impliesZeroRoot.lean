-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassageZero_psiNonneg_impliesZeroRoot
-- name    : Kyprianou.Ch03.firstPassageZero_psiNonneg_impliesZeroRoot
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T18:58:50.184806+00:00
-- url     : https://prove2.me/theorems/bb58529f-5e40-4dae-9330-0b4f1f1615f0
-- title:
--   Chapter 3 zero root: Nonnegative exponent on nonnegative half-line forces maximal root zero
-- statement:
--   Nonnegative exponent on nonnegative half-line forces maximal root zero; the root is still required to be a maximal nonnegative zero and all original process hypotheses are retained.
-- source:
--   Kyprianou (2006) Chapter 3 zero-root characterisation

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem firstPassageZero_psiNonneg_impliesZeroRoot
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega))) :
        forall phi : Real,
      (0 <= phi ∧ L.ψ phi = 0 ∧ (forall theta : Real, 0 <= theta ->
        L.ψ theta = 0 -> theta <= phi)) ->
      ((forall theta : Real, 0 <= theta ->
        0 <= L.ψ theta) -> phi = 0) := by
  sorry

end Kyprianou.Ch03
