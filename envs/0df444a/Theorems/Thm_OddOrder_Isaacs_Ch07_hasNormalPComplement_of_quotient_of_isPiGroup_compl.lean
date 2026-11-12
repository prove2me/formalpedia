-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_hasNormalPComplement_of_quotient_of_isPiGroup_compl
-- name    : OddOrder.Isaacs.Ch07.hasNormalPComplement_of_quotient_of_isPiGroup_compl
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:54:03.942105+00:00
-- url     : https://prove2.me/theorems/f70de1e8-ddd7-4f44-ba4a-5e5cd8034881
-- title:
--   A normal $p$-complement lifts across a normal $p'$-subgroup
-- statement:
--   Let $G$ be a finite group, $p$ a prime, and $N\trianglelefteq G$ a normal subgroup that is a $p'$-group (`IsPiGroup {q | q ≠ p} N`: no prime divisor of $|N|$ equals $p$). If $G/N$ has a normal $p$-complement, then $G$ has a normal $p$-complement.
--
--   The normal $p$-complement is the inverse image of the one in $G/N$. This is used in Step 3 of the minimal-counterexample argument for Isaacs's Theorem 7.1.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean#L998-L1103

import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJ_PComplement
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement

namespace OddOrder.Isaacs.Ch07

open scoped Pointwise

variable {G : Type*} [Group G]

section MinimalCounterexampleStepThree

theorem hasNormalPComplement_of_quotient_of_isPiGroup_compl
    [Finite G] {p : ℕ} [Fact p.Prime] {N : Subgroup G} [N.Normal]
    (hN_pi' : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ≠ p} N)
    (hQ : OddOrder.Isaacs.Ch05.HasNormalPComplement p (G ⧸ N)) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p G := by sorry

end MinimalCounterexampleStepThree

end OddOrder.Isaacs.Ch07
