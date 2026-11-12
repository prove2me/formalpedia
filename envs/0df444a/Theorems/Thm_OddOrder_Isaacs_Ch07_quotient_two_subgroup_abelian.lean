-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_quotient_two_subgroup_abelian
-- name    : OddOrder.Isaacs.Ch07.quotient_two_subgroup_abelian
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:48:40.620194+00:00
-- url     : https://prove2.me/theorems/abdb85a2-fe43-4a11-80dd-265344f51361
-- title:
--   The hypothesis that all $2$-subgroups are abelian descends to quotients
-- statement:
--   Let $G$ be a finite group and $K\trianglelefteq G$ a normal subgroup. Suppose every $2$-subgroup $S\le G$ is abelian ($xy=yx$ for all $x,y\in S$). Then every $2$-subgroup $S\le G/K$ is abelian.
--
--   A $2$-subgroup of $G/K$ is the image of a Sylow $2$-subgroup of its preimage, and that subgroup is abelian by the hypothesis. This is the Sylow-lift bridge needed to apply the reduced theorem to $G/K$ in Isaacs Thm 7.5.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7A2_NormalPThm75.lean#L1005-L1072

import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A1_JpGL2p
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

open scoped IsMulCommutative

variable {G : Type*} [Group G]

theorem quotient_two_subgroup_abelian
    {G : Type*} [Group G] [Finite G] {K : Subgroup G} [K.Normal]
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (S : Subgroup (G ⧸ K)) (hS2 : IsPGroup 2 S) :
    ∀ x y : ↥S, x * y = y * x := by sorry

end OddOrder.Isaacs.Ch07
