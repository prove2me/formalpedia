-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassageZero_consequence3
-- name    : Kyprianou.Ch03.firstPassageZero_consequence3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T15:03:17.68356+00:00
-- url     : https://prove2.me/theorems/3b28a0e5-4f35-4fff-a54c-d895bab7fc53
-- title:
--   Corollary 3.13 root/exact clause 3
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

theorem firstPassageZero_consequence3
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega))) :
        forall phi : Real,
      (0 <= phi ∧ L.ψ phi = 0 ∧ (forall theta : Real, 0 <= theta ->
        L.ψ theta = 0 -> theta <= phi)) ->
      ((phi = 0) <-> (forall theta : Real, 0 <= theta ->
        0 <= L.ψ theta)) := by
  sorry

end Kyprianou.Ch03
