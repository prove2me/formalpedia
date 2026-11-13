-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_K_eq_V_index_pq
-- name    : OddOrder.Peterfalvi.S16.K_eq_V_index_pq
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:31:40.23244+00:00
-- url     : https://prove2.me/theorems/196ba04d-24be-4721-9bd5-0edb3445fc31
-- title:
--   Peterfalvi (14.11): $K=V$ and $|M:K|=pq$
-- statement:
--   Let $G$ be a finite minimal simple odd-order group with no maximal subgroup of type V (`hnoV`), assume `hncH0C : S13.H0CNoncoherenceRefuter G`, and let `hyp` be a Peterfalvi §14 configuration for $G$ with primes $p,q$ and subgroup $V$. Let `Ldata : LHypothesis hyp` and `Mdata : MHypothesis hyp`. Then
--   $$K = V \quad\text{and}\quad e = pq,$$
--   where $K=$ `Mdata.K` (the Fitting-type kernel of the type-I maximal subgroup $M$) and $e=$ `Mdata.e` is the complement index $|M:K|$.
--
--   The equality $K=V$ follows from the contradiction of (14.11.1)--(14.11.4) if $K\neq V$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupM.lean#L1241-L1259

import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ConjugationFieldModel
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupMCore
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupM

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

theorem K_eq_V_index_pq [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (Ldata : LHypothesis hyp) (Mdata : MHypothesis hyp) :
    Mdata.K = hyp.base.V ∧ Mdata.e = hyp.base.p * hyp.base.q := by sorry

end OddOrder.Peterfalvi.S16
