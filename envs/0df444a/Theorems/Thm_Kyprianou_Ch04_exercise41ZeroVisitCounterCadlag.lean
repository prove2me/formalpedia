-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41ZeroVisitCounterCadlag
-- name    : Kyprianou.Ch04.exercise41ZeroVisitCounterCadlag
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T22:28:57.888236+00:00
-- url     : https://prove2.me/theorems/a9094338-0039-406d-9756-54c7b5f4067d
-- title:
--   Exercise 4.1(i): finite integer-valued cadlag zero-level visit count
-- statement:
--   For spectrally negative bounded-variation Levy input with its positive storage-model drift, the positive-time zero visits of X counted up to t are almost surely finite for every finite t. The resulting integer-valued counting process is right-continuous and admits left limits. Exercise 4.1(ii), the discontinuous-test-function change-of-variable formula, remains a separate obligation.
-- source:
--   Kyprianou (2006), first edition, Chapter 4, Exercise 4.1(i), printed pp. 105-106.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Exercise 4.1(i) (pp. 105-106): zero-level visit count has finite cadlag paths. -/
theorem exercise41ZeroVisitCounterCadlag
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift) :
    ∀ᵐ omega : Omega ∂P,
      (∀ t : NNReal,
        Set.Finite {s : NNReal | 0 < s ∧ s ≤ t ∧ L.X s omega = 0}) ∧
      (∀ t : NNReal,
        ContinuousWithinAt
          (fun u : NNReal =>
            (({s : NNReal | 0 < s ∧ s ≤ u ∧ L.X s omega = 0}).ncard : Real))
          (Set.Ici t) t) ∧
      (∀ t : NNReal, 0 < t →
        ∃ l : Real,
          Tendsto
            (fun u : NNReal =>
              (({s : NNReal | 0 < s ∧ s ≤ u ∧ L.X s omega = 0}).ncard : Real))
            (nhdsWithin t (Set.Iio t)) (nhds l)) := by
  sorry
end Kyprianou.Ch04
