-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch05_hasNormalPComplement_iff_isPGroup_normalizer_quotient_centralizer
-- name    : OddOrder.Isaacs.Ch05.hasNormalPComplement_iff_isPGroup_normalizer_quotient_centralizer
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:31:08.544447+00:00
-- url     : https://prove2.me/theorems/ccb8d972-a813-4e91-a481-fcf5bf340609
-- title:
--   Isaacs Theorem 5.26 (Frobenius): normal $p$-complement iff every $N_G(X)/C_G(X)$ is a $p$-group
-- statement:
--   Let $G$ be a finite group and $p$ a prime. Then $G$ has a normal $p$-complement if and only if for every $p$-subgroup $X\le G$ the quotient $N_G(X)/C_G(X)$ is a $p$-group.
--
--   This is Frobenius' normal $p$-complement theorem. The forward direction uses Lemma 5.27 (normalizers of $p$-subgroups inherit a normal $p$-complement, and then $N/C$ is a $p$-group); the reverse direction uses Lemma 5.28 to show every Sylow $p$-subgroup controls its own fusion, and Thm 5.25 to deduce the normal $p$-complement.
--
--   **Formalization Note** `HasNormalPComplement p G` means: there is a normal subgroup $N$ such that for every Sylow $p$-subgroup $P$, $N$ and $P$ are complements (`Subgroup.IsComplement' N P`). The quotient is `↥(normalizer X) ⧸ (centralizer X).subgroupOf (normalizer X)`, and being a $p$-group is `IsPGroup p`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch05_Transfer/Main.lean#L954-L1063

import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Basic
import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Main
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Nilpotent

open scoped commutatorElement

open scoped IsMulCommutative

namespace OddOrder.Isaacs.Ch05

open Pointwise

open scoped commutatorElement

variable {G : Type*} [Group G]

section

theorem hasNormalPComplement_iff_isPGroup_normalizer_quotient_centralizer
    [Finite G] {p : ℕ} [Fact p.Prime] :
    HasNormalPComplement p G ↔
    ∀ X : Subgroup G, IsPGroup p X →
      IsPGroup p (↥(Subgroup.normalizer (X : Set G)) ⧸
        (Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))) := by sorry

end

end OddOrder.Isaacs.Ch05
