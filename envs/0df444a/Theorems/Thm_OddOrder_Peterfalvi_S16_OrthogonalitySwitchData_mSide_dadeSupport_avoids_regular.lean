-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_OrthogonalitySwitchData_mSide_dadeSupport_avoids_regular
-- name    : OddOrder.Peterfalvi.S16.OrthogonalitySwitchData.mSide_dadeSupport_avoids_regular
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:22:53.627278+00:00
-- url     : https://prove2.me/theorems/7571a3a3-c302-47fd-ae03-16d2bc6b7109
-- title:
--   Peterfalvi (13.19.a): the Dade support of a type-I maximal $M$ avoids the regular set $\hat W^G$
-- statement:
--   Let $G$ be a finite minimal simple odd-order group with no maximal subgroup of type V (`hnoV`), assume `hncH0C : S13.H0CNoncoherenceRefuter G`, and let `hyp` be a Peterfalvi §14 configuration. Let $M$ be a maximal subgroup of $G$ and `dataM : TypeICoherent78Data M` the (7.8) coherence data for the type-I maximal subgroup $M$. Then every element $x$ of the $G$-conjugacy saturation of $W \setminus (W_1\cup W_2)$ (`conjClassSet (W \ (W₁ ∪ W₂))`) lies outside the Dade support $\tilde A(M)$ of $M$:
--   $$\forall x\in (W\setminus(W_1\cup W_2))^G,\quad x\notin \tilde A(M),$$
--   where $\tilde A(M)$ is `(dataM.h78 hG).hyp76.hyp71.hyp.dadeSupport`.
--
--   The reason is that every such $x$ has order dividing $pq$, so it is coprime to $|M_F|$, whereas every element of $\tilde A(M)$ is singular for the primes dividing $|M_F|$. The statement is used for type-I maximal subgroups not conjugate to those containing $W$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/CoherentEtaOrthogonality.lean#L252-L312

import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupL
import Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion
import Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentEtaOrthogonality

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace OrthogonalitySwitchData

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in

theorem mSide_dadeSupport_avoids_regular [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    {hyp : Hypothesis (G := G)}
    {M : Subgroup G} (hMmax : M ∈ maximalSubgroups G) (dataM : TypeICoherent78Data M) :
    ∀ x ∈ conjClassSet
        ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G))),
      x ∉ (dataM.h78 hG).hyp76.hyp71.hyp.dadeSupport := by sorry

end OrthogonalitySwitchData

end OddOrder.Peterfalvi.S16
