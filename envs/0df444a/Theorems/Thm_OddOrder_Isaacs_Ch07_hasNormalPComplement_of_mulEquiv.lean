-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_hasNormalPComplement_of_mulEquiv
-- name    : OddOrder.Isaacs.Ch07.hasNormalPComplement_of_mulEquiv
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:53:03.883137+00:00
-- url     : https://prove2.me/theorems/d98d4419-7f45-408e-87b1-5c8c56a87823
-- title:
--   Normal $p$-complements transfer along group isomorphisms
-- statement:
--   We say a finite group $X$ has a *normal $p$-complement* (`HasNormalPComplement p X`) if there is a normal subgroup $N\trianglelefteq X$ that is a complement (`IsComplement'`) of every Sylow $p$-subgroup of $X$.
--
--   Let $G'$ and $H$ be finite groups, $p$ a prime, and $e:G'\simeq H$ a group isomorphism. If $G'$ has a normal $p$-complement, then so does $H$.
--
--   This is a routine transport lemma used in the quotient and correspondence arguments for Isaacs's Theorem 7.1.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJ_PComplement.lean#L167-L225

import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJClose
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJ_PComplement

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped commutatorElement

theorem hasNormalPComplement_of_mulEquiv
    {G' H : Type*} [Group G'] [Group H]
    [Finite G'] [Finite H] {p : ℕ} [Fact p.Prime] (e : G' ≃* H)
    (hG : OddOrder.Isaacs.Ch05.HasNormalPComplement p G') :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p H := by sorry

end OddOrder.Isaacs.Ch07
