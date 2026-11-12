-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_omega1ZCenterOpCore_relIndex_inter_A_le
-- name    : OddOrder.Isaacs.Ch07.omega1ZCenterOpCore_relIndex_inter_A_le
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:50:08.339005+00:00
-- url     : https://prove2.me/theorems/946350ac-5575-40ce-8682-fe256ed6a7ea
-- title:
--   Isaacs 7.6, Step 7: $|V : V\cap A|\le p$ for $A\in E(P)$
-- statement:
--   Let $G$ be a finite group and $p$ a prime. Write $O_p(G)$ for the largest normal $p$-subgroup (`opCore p G`), $O_{p'}(G)$ for the largest normal $p'$-subgroup (`oPiCore {q | q ≠ p} G`), and $Z(\cdot)$ for the center, viewed as a subgroup of $G$. Put $U=O_p(G)$ and $V=\Omega_1(Z(O_p(G)))$ (`omega1ZCenterOpCore G p`).
--
--   Let $P$ be a Sylow $p$-subgroup of $G$ and $A\in E(P)$. If $|A : A\cap U|\le p$, then
--   $$|V : V\cap A|\le p.$$
--
--   This is Step 7 of the proof of Isaacs's Theorem 7.6, feeding the application of Theorem 7.5 in Step 8.
--
--   **Formalization Note.** $O_p(G)$ appears both as `opCore p G` and as `oPiCore {p} G` (the $\pi$-core for $\pi=\{p\}$); `Subgroup.relIndex H K` is the index $|K : H\cap K|$. "$p$-separable" is the instance `IsPiSeparable {p} G`. $E(P)$ is `maxElemAbelianIn P p`, the elementary abelian $p$-subgroups of $P$ of maximal order, and $J(P)$ is `Subgroup.thompsonJ P p`, the subgroup they generate.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ.lean#L423-L562

import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B1_NormalJ_Setup

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

theorem omega1ZCenterOpCore_relIndex_inter_A_le
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {A : Subgroup G}
    (hA : A ∈ Subgroup.maxElemAbelianIn (P : Subgroup G) p)
    (hA_D_relIndex : (OddOrder.Isaacs.Ch01.opCore p G).relIndex A ≤ p) :
    A.relIndex (omega1ZCenterOpCore G p) ≤ p := by sorry

end OddOrder.Isaacs.Ch07
