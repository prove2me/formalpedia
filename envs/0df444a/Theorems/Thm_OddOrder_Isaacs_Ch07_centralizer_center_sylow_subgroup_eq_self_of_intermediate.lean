-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_centralizer_center_sylow_subgroup_eq_self_of_intermediate
-- name    : OddOrder.Isaacs.Ch07.centralizer_center_sylow_subgroup_eq_self_of_intermediate
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:51:16.934566+00:00
-- url     : https://prove2.me/theorems/3f9562a1-cfa3-4fd4-90bc-8db50664fcc1
-- title:
--   Isaacs 7.6, Step 3: $C_H(Z(S))=S$ for $S=H\cap P$ with $O_p(G)\le H$
-- statement:
--   Let $G$ be a finite group and $p$ a prime. Write $O_p(G)$ for the largest normal $p$-subgroup (`opCore p G`), $O_{p'}(G)$ for the largest normal $p'$-subgroup (`oPiCore {q | q ≠ p} G`), and $Z(\cdot)$ for the center, viewed as a subgroup of $G$.
--
--   Assume $G$ is $p$-separable, $O_{p'}(G)=1$, and $P$ is a Sylow $p$-subgroup of $G$ with $C_G(Z(P))=P$. Let $H\le G$ be a subgroup containing $O_p(G)$, and let $S$ be a Sylow $p$-subgroup of the group $H$ whose underlying subgroup of $H$ equals $H\cap P$ (as a subgroup of $H$). Then
--   $$C_H(Z(S))=S,$$
--   where $Z(S)$ is the center of $S$ and the centralizer is taken in $H$.
--
--   This is the transfer of hypothesis (v) of Isaacs's Theorem 7.6 to intermediate subgroups, as needed in Step 3 for the induction hypothesis.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJClose.lean#L140-L260

import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B1_NormalJ_Setup
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJClose

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

theorem centralizer_center_sylow_subgroup_eq_self_of_intermediate
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (P : Sylow p G)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    {H : Subgroup G}
    (hU_le_H : OddOrder.Isaacs.Ch01.opCore p G ≤ H)
    (S : Sylow p ↥H)
    (hS_eq : (S : Subgroup ↥H) = (H ⊓ (P : Subgroup G)).subgroupOf H) :
    Subgroup.centralizer
        (((Subgroup.center (S : Subgroup ↥H)).map (S : Subgroup ↥H).subtype) : Set ↥H)
      = (S : Subgroup ↥H) := by sorry

end OddOrder.Isaacs.Ch07
