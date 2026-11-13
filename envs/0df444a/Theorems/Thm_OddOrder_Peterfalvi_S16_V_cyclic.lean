-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_V_cyclic
-- name    : OddOrder.Peterfalvi.S16.V_cyclic
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:37:10.748199+00:00
-- url     : https://prove2.me/theorems/4cde9b3d-ff3b-4dd4-a699-185bae7d3a7b
-- title:
--   Peterfalvi (13.2.a) for $T$: the complement $V$ is cyclic
-- statement:
--   Let $G$ be a finite minimal simple odd-order group (`IsMinimalSimpleOdd G`) with no maximal subgroup of type V (`hnoV`), and assume the noncoherence refuter `OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G` (`hncH0C`). Let `hyp` be a Peterfalvi §14 configuration (`OddOrder.Peterfalvi.S16.Hypothesis`) for $G$. Then the subgroup $V$ of `hyp.base` is cyclic:
--   $$V \text{ is cyclic}\quad(\texttt{IsCyclic ↥hyp.base.V}).$$
--
--   Here $V$ is the abelian Frobenius kernel complement on the $T$-side; the statement is the $T$-side analogue of the cyclicity of $U$. It is used to show that $K = V$ is cyclic in (14.11).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/BetaVanishing.lean#L318-L423

import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupM
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentEtaOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_BetaVanishing

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

open scoped IsMulCommutative in

theorem V_cyclic [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) : IsCyclic ↥hyp.base.V := by sorry

end OddOrder.Peterfalvi.S16
