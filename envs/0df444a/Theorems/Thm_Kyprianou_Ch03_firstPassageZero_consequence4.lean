-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassageZero_consequence4
-- name    : Kyprianou.Ch03.firstPassageZero_consequence4
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T15:03:22.875489+00:00
-- url     : https://prove2.me/theorems/46b1c6f9-6d42-472d-abc2-e7e10be5fd2f
-- title:
--   Corollary 3.13 root/exact clause 4
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

theorem firstPassageZero_consequence4
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
        ((phi = 0) <-> 0 <= (∫ omega, L.X 1 omega ∂P))) := by
  sorry

end Kyprianou.Ch03
