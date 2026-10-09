-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_indep_prefix_next_singleton
-- name    : NestedSeatAlloc.IntPolicy.indep_prefix_next_singleton
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T14:08:41.611423+00:00
-- url     : https://prove2.me/theorems/99547609-529a-4a12-a1cc-b609604801ec
-- title:
--   The finite higher-fare demand vector is independent of the next-class singleton demand vector
-- statement:
--   # Finite higher-fare demands are independent of the new-class demand
--
--   Model assumption hM.indep is the independence of all indexed class demands
--   X i. The old higher-fare vector U comprises X i for i in Finset.Icc 1 k.
--   The next-class vector V comprises the singleton index k+1.
--
--   The two index sets are disjoint because every i in Icc 1 k satisfies
--   i<=k whereas the singleton contains only k+1. The Mathlib theorem
--   ProbabilityTheory.iIndepFun.indepFun_finset specialises global
--   iIndepFun to independence of the two finite product vectors, given
--   that all coordinates are measurable. The hM.meas field supplies exactly
--   the coordinate measurability.
--
--   The lemma leaves V as a singleton product vector. To get independence
--   of U from Z(ω)=X(k+1,ω), compose the second variable with evaluation at
--   the singleton index, using IndepFun.comp or an equivalent measurable
--   postcomposition. This composition and the product-law decomposition
--   provide the independence bridge required by
--   expRevenue_eq_integral_condRevenue.
--
--   The exact accepted type of iIndepFun.indepFun_finset was returned from
--   the remote signature probe job 583afef9-1bd0-46b7-b4df-e9bd3cae7018.
--   The source is meant for remote verification only.
-- source:
--   # Finite higher-fare demands are independent of the new-class demand
--
--   Model assumption hM.indep is the independence of all indexed class demands
--   X i. The old higher-fare vector U comprises X i for i in Finset.Icc 1 k.
--   The next-class vector V comprises the singleton index k+1.
--
--   The two index sets are disjoint because every i in Icc 1 k satisfies
--   i<=k whereas the singleton contains only k+1. The Mathlib theorem
--   ProbabilityTheory.iIndepFun.indepFun_finset specialises global
--   iIndepFun to independence of the two finite product vectors, given
--   that all coordinates are measurable. The hM.meas field supplies exactly
--   the coordinate measurability.
--
--   The lemma leaves V as a singleton product vector. To get independence
--   of U from Z(ω)=X(k+1,ω), compose the second variable with evaluation at
--   the singleton index, using IndepFun.comp or an equivalent measurable
--   postcomposition. This composition and the product-law decomposition
--   provide the independence bridge required by
--   expRevenue_eq_integral_condRevenue.
--
--   The exact accepted type of iIndepFun.indepFun_finset was returned from
--   the remote signature probe job 583afef9-1bd0-46b7-b4df-e9bd3cae7018.
--   The source is meant for remote verification only.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.indep_prefix_next_singleton
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ) (hM : IsSeatModel P X f) (k : ℕ) :
    IndepFun
      (fun ω : Ω => fun i : (Finset.Icc 1 k) => X i.1 ω)
      (fun ω : Ω => fun i : ({k + 1} : Finset ℕ) => X i.1 ω) P := by sorry
