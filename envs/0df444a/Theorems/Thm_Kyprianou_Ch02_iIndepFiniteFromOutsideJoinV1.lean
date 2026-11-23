-- Prove2me | Theorems.Thm_Kyprianou_Ch02_iIndepFiniteFromOutsideJoinV1
-- name    : Kyprianou.Ch02.iIndepFiniteFromOutsideJoinV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T12:16:05.440979+00:00
-- url     : https://prove2.me/theorems/d8c19028-1bfb-49de-a7ec-baae5b9db37d
-- title:
--   Finite joint independence from independence of each sigma algebra against every complementary finite join
-- statement:
--   A finite family of sub-σ-algebras of an ambient measurable space is jointly independent if each σ-algebra is independent of the join of any subfamily excluding itself. The proof uses iIndep_iff and induction over finite selected index sets, applying Indep.indepSet_of_measurableSet and IndepSet.measure_inter_eq_mul at each insertion. This is a general pure probability result, stronger than pairwise independence, needed to apply existing Proved disjoint-region PRM sigma-algebra independence to all time strips jointly.
-- source:
--   Mathlib ProbabilityTheory.iIndep_iff and independent sigma-algebra factorisation, applied in Kyprianou (2006) Eq. (2.3)

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.iIndepFiniteFromOutsideJoinV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ)
    (m : Fin n → MeasurableSpace Ω)
    (hm : ∀ i, m i ≤ (inferInstance : MeasurableSpace Ω))
    (hInd : ∀ (i : Fin n) (s : Finset (Fin n)), i ∉ s →
      ProbabilityTheory.Indep (m i) (⨆ j ∈ s, m j) P) :
    ProbabilityTheory.iIndep m P := by sorry
