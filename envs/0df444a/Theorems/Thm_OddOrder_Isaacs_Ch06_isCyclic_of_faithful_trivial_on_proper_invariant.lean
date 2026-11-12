-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch06_isCyclic_of_faithful_trivial_on_proper_invariant
-- name    : OddOrder.Isaacs.Ch06.isCyclic_of_faithful_trivial_on_proper_invariant
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:34:49.949209+00:00
-- url     : https://prove2.me/theorems/fed6ddfe-73af-47ca-af0e-2f435c38a8ea
-- title:
--   Isaacs Lemma 6.20: a faithful coprime abelian action that is trivial on proper invariant subgroups is cyclic
-- statement:
--   Let $A$ be a finite abelian group acting faithfully by automorphisms on a finite group $N$ (`MulDistribMulAction A N`, `FaithfulSMul A N`), with $\gcd(|A|,|N|)=1$. Suppose that for every $A$-invariant subgroup $M\le N$ with $M\ne N$, the group $A$ acts trivially on $M$ ($a\cdot n=n$ for all $a\in A$, $n\in M$). Then $A$ is cyclic.
--
--   This is Isaacs Lemma 6.20.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch06_FrobeniusActions/FrobeniusGroup.lean#L1388-L1458

import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusActionTI
import Definitions.Def_OddOrder_Mathlib_Subgroup
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup

namespace OddOrder.Isaacs.Ch06

open scoped IsMulCommutative

section

universe uA uN

theorem isCyclic_of_faithful_trivial_on_proper_invariant
    {A : Type uA} {N : Type uN} [Group A] [Finite A] [IsMulCommutative A]
    [Group N] [Finite N] [MulDistribMulAction A N] [FaithfulSMul A N]
    (hCop : Nat.Coprime (Nat.card A) (Nat.card N))
    (hproper :
      ∀ M : Subgroup N,
        (∀ a : A, ∀ n ∈ M, a • n ∈ M) →
        M ≠ ⊤ →
        ∀ a : A, ∀ n ∈ M, a • n = n) :
    IsCyclic A := by sorry

end

end OddOrder.Isaacs.Ch06
