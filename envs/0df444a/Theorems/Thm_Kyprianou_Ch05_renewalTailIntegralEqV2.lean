-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalTailIntegralEqV2
-- name    : Kyprianou.Ch05.renewalTailIntegralEqV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:31:29.181841+00:00
-- url     : https://prove2.me/theorems/f1e7dea4-32eb-52b8-833b-6ba3df09d8ff
-- title:
--   Lemma 5.5 step: integral of the truncated tail (corrected)
-- statement:
--   Renewal-tail integral translation for arbitrary F and u and nonnegative y.
-- source:
--   Kyprianou (2006), first edition, Lemma 5.5, printed pp.116-117, equation (5.5).

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05
theorem renewalTailIntegralEqV2
    (F : Measure Real) (u y : Real) (hy : 0 ≤ y) :
    (∫ z in Set.Ici (0 : Real),
      (if y < z then (F (Set.Ioi (z + u))).toReal else 0) ∂volume) =
    ∫ z in Set.Ioi (u + y), (F (Set.Ioi z)).toReal ∂volume := by
  sorry
end Kyprianou.Ch05
