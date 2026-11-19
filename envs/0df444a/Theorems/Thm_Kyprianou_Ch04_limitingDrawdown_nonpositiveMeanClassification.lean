-- Prove2me | Theorems.Thm_Kyprianou_Ch04_limitingDrawdown_nonpositiveMeanClassification
-- name    : Kyprianou.Ch04.limitingDrawdown_nonpositiveMeanClassification
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T13:03:14.37766+00:00
-- url     : https://prove2.me/theorems/57104284-8e35-4d12-9313-25e71b20b99d
-- title:
--   limitingDrawdownTransformAndDrift: Nonpositive mean equivalence with lower-unbounded paths
-- statement:
--   Nonpositive mean equivalence with lower-unbounded paths. An exact standalone source conjunct from the complete corrected Chapter 4 theorem, retaining all original binders and assumptions.
-- source:
--   Kyprianou (2006), first edition, Chapter 4, Corollary 4.9, printed p. 100

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Corollary 4.9 (p. 100): limiting transform of running supremum minus X, and drift classification. -/
theorem limitingDrawdown_nonpositiveMeanClassification
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotNegativeSubordinator :
      ¬ (∀ᵐ omega : Omega ∂P,
        Antitone (fun t : NNReal => L.X t omega))) :
    let nonnegativeSlope : Real :=
      max 0 (sInf ((fun theta : Real => L.ψ theta / theta) '' Set.Ioi 0))
    let meanNonpositive : Prop :=
      forall epsilon : Real, 0 < epsilon ->
        exists theta : Real, 0 < theta ∧ L.ψ theta < epsilon * theta
    (meanNonpositive ↔
      (P {omega : Omega |
        ¬ BddBelow (Set.range
          (fun t : NNReal => L.X t omega))}).toReal = 1) := by
  sorry
end Kyprianou.Ch04
