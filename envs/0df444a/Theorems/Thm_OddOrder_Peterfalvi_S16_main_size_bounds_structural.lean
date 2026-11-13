-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_main_size_bounds_structural
-- name    : OddOrder.Peterfalvi.S16.main_size_bounds_structural
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:26:41.085603+00:00
-- url     : https://prove2.me/theorems/a1325242-7997-4918-a677-adeba817ffd7
-- title:
--   Peterfalvi (14.11.1), structural half: $k>2pv$ and $(k-1)/e>(v-1)/p$ when $K\neq V$
-- statement:
--   Let $G$ be a finite minimal simple odd-order group with no maximal subgroup of type V (`hnoV`), assume `hncH0C : S13.H0CNoncoherenceRefuter G`, let `hyp` be a Peterfalvi §14 configuration with parameters $p,q,v$, and `Mdata : MHypothesis hyp` with kernel $K=$ `Mdata.K`, $k=|K|$ and complement index $e$. Assume $K\neq V$ and $e\le pq$. Then
--   $$k>2pv\qquad\text{and}\qquad \frac{k-1}{e}>\frac{v-1}{p}\ \text{ in }\mathbb{Q}$$
--   (with $k-1$, $v-1$ computed in $\mathbb{N}$).
--
--   The bound $k>2pv$ comes from the factorization $k=vx$ with $x\neq1$, $x\equiv1\pmod p$, and $x$ odd, so $x\ge 2p+1$. The quotient bound follows from $k>2pv$, $e\le pq$, $q<p$ by cross-multiplication. The third inequality of (14.11.1), $(v-1)/p>(u-1)/q$, is not part of this statement.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupMCore.lean#L600-L731

import Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentEtaOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentProjectionRigidity
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupL
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupMCore

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

theorem main_size_bounds_structural [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp)
    (hne : Mdata.K ≠ hyp.base.V)
    (he_le : Mdata.e ≤ hyp.base.p * hyp.base.q) :
    Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) := by sorry

end OddOrder.Peterfalvi.S16
