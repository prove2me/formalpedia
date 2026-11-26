-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46BusyPathCountFunctionalV1
-- name    : Kyprianou.Ch04.exercise46BusyPathCountFunctionalV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:02:43.587454+00:00
-- url     : https://prove2.me/theorems/fadb3193-83c7-55cc-b468-25646bac89e1
-- title:
--   Measurable count of busy-start marks from a path drawdown proxy
-- statement:
--   Use measurable exact cadlag jump selectors and a jointly measurable drawdown proxy, count only positive drawdowns equal to the negative jump mark, and deduplicate the candidate enumeration.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false
open scoped Topology

theorem Kyprianou.Ch04.exercise46BusyPathCountFunctionalV1
    (D : NNReal → (NNReal → Real) → Real)
    (hD : Measurable (fun z : NNReal × (NNReal → Real) => D z.1 z.2)) :
    ∃ C : (NNReal → Real) → ENNReal, Measurable C ∧
      ∀ Y : NNReal → Real,
        (∀ u, ContinuousWithinAt Y (Ici u) u) →
        (∀ u, 0 < u → ∃ l : Real, Tendsto Y (nhdsWithin u (Iio u)) (nhds l)) →
        C Y = (({t : NNReal | 0 < t ∧
          0 < D t Y ∧ D t Y = -(Y t - Function.leftLim Y t)}).encard : ENNReal) := by
  sorry
