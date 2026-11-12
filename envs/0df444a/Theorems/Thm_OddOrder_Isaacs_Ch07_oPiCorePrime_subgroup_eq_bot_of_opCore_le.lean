-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_oPiCorePrime_subgroup_eq_bot_of_opCore_le
-- name    : OddOrder.Isaacs.Ch07.oPiCorePrime_subgroup_eq_bot_of_opCore_le
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:51:27.604617+00:00
-- url     : https://prove2.me/theorems/0383567a-57d5-4a66-baea-e89e7e3ce74a
-- title:
--   Isaacs 7.6, Step 1(b): $O_{p'}(H)=1$ for $O_p(G)\le H\le G$
-- statement:
--   Let $G$ be a finite group and $p$ a prime. Write $O_p(G)$ for the largest normal $p$-subgroup (`opCore p G`), $O_{p'}(G)$ for the largest normal $p'$-subgroup (`oPiCore {q | q ≠ p} G`), and $Z(\cdot)$ for the center, viewed as a subgroup of $G$.
--
--   Assume $G$ is $p$-separable and $O_{p'}(G)=1$. Then for every subgroup $H$ with $O_p(G)\le H\le G$,
--   $$O_{p'}(H)=1,$$
--   where $O_{p'}(H)$ is computed in the group $H$.
--
--   This is Step 1(b) of the proof of Isaacs's Theorem 7.6; it lets the induction hypothesis be applied to such subgroups $H$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJClose.lean#L57-L138

import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B1_NormalJ_Setup
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJClose

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

theorem oPiCorePrime_subgroup_eq_bot_of_opCore_le
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    {H : Subgroup G} (hUH : OddOrder.Isaacs.Ch01.opCore p G ≤ H) :
    OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} (↥H) = ⊥ := by sorry

end OddOrder.Isaacs.Ch07
