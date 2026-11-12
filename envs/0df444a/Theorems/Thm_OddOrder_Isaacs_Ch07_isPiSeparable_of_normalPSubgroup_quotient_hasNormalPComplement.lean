-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_isPiSeparable_of_normalPSubgroup_quotient_hasNormalPComplement
-- name    : OddOrder.Isaacs.Ch07.isPiSeparable_of_normalPSubgroup_quotient_hasNormalPComplement
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:54:56.486611+00:00
-- url     : https://prove2.me/theorems/ae546803-e569-4c95-ab52-3dfd9618097d
-- title:
--   $p$-separability from a normal $p$-subgroup with quotient having a normal $p$-complement
-- statement:
--   Let $G$ be a finite group, $p$ a prime, and $U\trianglelefteq G$ a normal subgroup that is a $p$-group. If $G/U$ has a normal $p$-complement, then $G$ is $\{p\}$-separable (`IsPiSeparable {p} G`), i.e. $p$-separable.
--
--   This is the $p$-separability consequence of Step 2 in the proof of Isaacs's Theorem 7.1; it makes Theorem 7.6 available later in the argument.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean#L850-L992

import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJ_PComplement
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement

namespace OddOrder.Isaacs.Ch07

open scoped Pointwise

variable {G : Type*} [Group G]

section MinimalCounterexampleStepTwo

theorem isPiSeparable_of_normalPSubgroup_quotient_hasNormalPComplement
    [Finite G] {p : ℕ} [Fact p.Prime] {U : Subgroup G} [U.Normal]
    (hU_p : IsPGroup p U)
    (hQ : OddOrder.Isaacs.Ch05.HasNormalPComplement p (G ⧸ U)) :
    OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G := by sorry

end MinimalCounterexampleStepTwo

end OddOrder.Isaacs.Ch07
