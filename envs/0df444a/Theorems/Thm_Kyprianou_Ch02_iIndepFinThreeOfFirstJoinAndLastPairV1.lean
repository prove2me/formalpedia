-- Prove2me | Theorems.Thm_Kyprianou_Ch02_iIndepFinThreeOfFirstJoinAndLastPairV1
-- name    : Kyprianou.Ch02.iIndepFinThreeOfFirstJoinAndLastPairV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:47:20.485552+00:00
-- url     : https://prove2.me/theorems/9226c065-6d17-4f52-b627-fb861be3be08
-- title:
--   Three sigma-algebras are independent if the first is independent of the last two jointly and the last two are independent
-- statement:
--   For a probability measure and three sigma-algebras, independence of the first from the join of the last two, together with independence of the last two, implies joint independence.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem iIndepFinThreeOfFirstJoinAndLastPairV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (m : Fin 3 → MeasurableSpace Ω)
    (h0 : Indep (m 0) (m 1 ⊔ m 2) P)
    (h12 : Indep (m 1) (m 2) P) :
    iIndep m P := by sorry
end Kyprianou.Ch02
