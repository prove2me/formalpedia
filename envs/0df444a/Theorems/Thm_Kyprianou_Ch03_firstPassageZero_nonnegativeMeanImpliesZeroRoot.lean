-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassageZero_nonnegativeMeanImpliesZeroRoot
-- name    : Kyprianou.Ch03.firstPassageZero_nonnegativeMeanImpliesZeroRoot
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T19:00:02.277365+00:00
-- url     : https://prove2.me/theorems/5f1f9d6b-d7f3-49a4-9411-50a3f822f66b
-- title:
--   Chapter 3 first-passage zero-root: Nonnegative mean increment implies the maximal nonnegative Laplace-exponent zero root is zero under integrability
-- statement:
--   Nonnegative mean increment implies the maximal nonnegative Laplace-exponent zero root is zero under integrability. Every original stochastic-process and root hypothesis is retained.
-- source:
--   Kyprianou (2006) Chapter 3 first-passage zero-root criterion

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem firstPassageZero_nonnegativeMeanImpliesZeroRoot
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega))) :
        forall phi : Real,
      (0 <= phi ∧ L.ψ phi = 0 ∧ (forall theta : Real, 0 <= theta ->
        L.ψ theta = 0 -> theta <= phi)) ->
      (Integrable (L.X 1) P ->
        ((0 <= (∫ omega, L.X 1 omega ∂P)) -> phi = 0)) := by
  sorry

end Kyprianou.Ch03
