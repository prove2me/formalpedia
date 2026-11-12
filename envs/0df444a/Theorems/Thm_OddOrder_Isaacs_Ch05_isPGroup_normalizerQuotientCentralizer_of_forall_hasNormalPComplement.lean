-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch05_isPGroup_normalizerQuotientCentralizer_of_forall_hasNormalPComplement
-- name    : OddOrder.Isaacs.Ch05.isPGroup_normalizerQuotientCentralizer_of_forall_hasNormalPComplement
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:31:13.698117+00:00
-- url     : https://prove2.me/theorems/8f8820d2-8fae-4ca1-bee5-7acd70d65f60
-- title:
--   Isaacs Lemma 5.27 (part 2): normalizers with normal $p$-complement give $p$-group quotients $N_G(X)/C_G(X)$
-- statement:
--   Let $G$ be a finite group and $p$ a prime. Suppose that for every nontrivial $p$-subgroup $X\ne1$ of $G$, the normalizer $N_G(X)$ has a normal $p$-complement. Then for every $p$-subgroup $X\le G$ (including the trivial one), the quotient $N_G(X)/C_G(X)$ is a $p$-group.
--
--   For $X=1$ the quotient is trivial. For $X\ne1$, take a normal $p$-complement $K'$ of $N_G(X)$: $K'$ and $X$ are normal in $N_G(X)$ with trivial intersection, so $[K',X]=1$, hence $K'\le C_G(X)$, and $N_G(X)/C_G(X)$ is a quotient of the $p$-group $N_G(X)/K'$.
--
--   **Formalization Note** `HasNormalPComplement p ↥(normalizer X)` means $N_G(X)$ has a normal subgroup that is a complement to every Sylow $p$-subgroup; the quotient is `↥(normalizer X) ⧸ (centralizer X).subgroupOf (normalizer X)`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch05_Transfer/Main.lean#L480-L579

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

theorem isPGroup_normalizerQuotientCentralizer_of_forall_hasNormalPComplement
    [Finite G] {p : ℕ} [Fact p.Prime]
    (h : ∀ X : Subgroup G, X ≠ ⊥ → IsPGroup p X →
        HasNormalPComplement p ↥(Subgroup.normalizer (X : Set G)))
    (X : Subgroup G) (hXp : IsPGroup p X) :
    IsPGroup p (↥(Subgroup.normalizer (X : Set G)) ⧸
      (Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))) := by sorry

end

end OddOrder.Isaacs.Ch05
