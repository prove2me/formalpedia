-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch06_isNilpotent_of_isFrobeniusAction_of_prime_card_aux
-- name    : OddOrder.Isaacs.Ch06.isNilpotent_of_isFrobeniusAction_of_prime_card_aux
-- status  : Open
-- author  : @burkh4rt
-- created : 2026-11-12T05:54:21.263497+00:00
-- url     : https://prove2.me/theorems/8b4cb6d0-0a79-4825-8b9f-58f5b6490d21
-- title:
--   Induction core for Isaacs Theorem 6.24: a prime-order Frobenius actor forces a nilpotent group
-- statement:
--   Let $A$ be a finite group of prime order $p$. Then for every $k\in\mathbb{N}$ and every finite group $N$ with $|N|\le k$ on which $A$ acts by automorphisms (`MulDistribMulAction A N`) in a Frobenius manner (`IsFrobeniusAction A N`: every nonidentity element of $A$ fixes only the identity of $N$), the group $N$ is nilpotent.
--
--   This is the strong-induction-on-$|N|$ core of Isaacs Thm 6.24 (a group admitting a Frobenius action by a group of prime order is nilpotent); the induction is organized with the bound $|N|\le k$.
--
--   **Formalization Note** The quantifier over the group $N$ (in an arbitrary universe) and the instances $\texttt{[Group N] [Finite N] [MulDistribMulAction A N]}$ appear inside the conclusion, so the statement is $\forall k,\ \forall N,\ |N|\le k\to\text{Frobenius}\to\text{nilpotent}$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch06_FrobeniusActions/KernelNilpotent.lean#L168-L357

import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Basic
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusActionTI
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03c_Thm37
import Mathlib.GroupTheory.Nilpotent

namespace OddOrder.Isaacs.Ch06

open OddOrder.Isaacs.Ch03 (IsAInvariant)

open scoped Pointwise

section

theorem isNilpotent_of_isFrobeniusAction_of_prime_card_aux
    {A : Type*} [Group A] [Finite A] {p : ℕ} (hp : p.Prime) (hcardA : Nat.card A = p) :
    ∀ (k : ℕ) (N : Type*) [Group N] [Finite N] [MulDistribMulAction A N],
      Nat.card N ≤ k → IsFrobeniusAction A N → Group.IsNilpotent N := by sorry

end

end OddOrder.Isaacs.Ch06
