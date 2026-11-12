-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_normal_thompsonJ_of_le_opCore
-- name    : OddOrder.Isaacs.Ch07.normal_thompsonJ_of_le_opCore
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:50:08.581643+00:00
-- url     : https://prove2.me/theorems/e486918d-0c65-46aa-a6b4-6f6456a0d1fb
-- title:
--   Isaacs Theorem 7.6, Step 8: $J(P)\le O_p(G)$ implies $J(P)\trianglelefteq G$
-- statement:
--   Let $G$ be a finite group, $p$ a natural number, and $P$ a Sylow $p$-subgroup of $G$. If the Thompson subgroup $J(P)$ is contained in $O_p(G)$, then $J(P)$ is normal in $G$:
--   $$J(P)\le O_p(G)\ \Longrightarrow\ J(P)\trianglelefteq G.$$
--
--   From $J(P)\le L=O_p(G)$ and the Step 2 / Thm 7.2 bridge one gets $J(L)=J(P)$. For $g\in G$ and a maximal-order elementary abelian subgroup $E$ of $L$, $gEg^{-1}$ is again such a subgroup, so the join defining $J(L)$ is $G$-stable.
--
--   **Formalization Note** $J(P)$ is `Subgroup.thompsonJ P p`, the join of the elementary abelian $p$-subgroups of $P$ of maximal order; $O_p(G)$ is `Ch01.opCore p G`, the intersection of all Sylow $p$-subgroups. The statement does not assume $p$ is prime.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ.lean#L668-L709

import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B1_NormalJ_Setup

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

theorem normal_thompsonJ_of_le_opCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} (P : Sylow p G)
    (h_le : Subgroup.thompsonJ (P : Subgroup G) p ≤ OddOrder.Isaacs.Ch01.opCore p G) :
    (Subgroup.thompsonJ (P : Subgroup G) p).Normal := by sorry

end OddOrder.Isaacs.Ch07
