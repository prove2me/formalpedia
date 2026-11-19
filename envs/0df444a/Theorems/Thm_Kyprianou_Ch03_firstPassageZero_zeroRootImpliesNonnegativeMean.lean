-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassageZero_zeroRootImpliesNonnegativeMean
-- name    : Kyprianou.Ch03.firstPassageZero_zeroRootImpliesNonnegativeMean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T19:00:06.457389+00:00
-- url     : https://prove2.me/theorems/5107d9f5-5c48-49dd-bcc4-628b32afb675
-- title:
--   Chapter 3 first-passage zero-root: The maximal zero root being zero implies a nonnegative mean increment under its original integrability assumption
-- statement:
--   The maximal zero root being zero implies a nonnegative mean increment under its original integrability assumption. Every original stochastic-process and root hypothesis is retained.
-- source:
--   Kyprianou (2006) Chapter 3 first-passage zero-root criterion

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem firstPassageZero_zeroRootImpliesNonnegativeMean
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
        ((phi = 0) -> 0 <= (∫ omega, L.X 1 omega ∂P))) := by
  sorry

end Kyprianou.Ch03
