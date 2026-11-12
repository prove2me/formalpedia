-- Prove2me | Theorems.Thm_OddOrder_Algebra_exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed
-- name    : OddOrder.Algebra.exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:06:50.071561+00:00
-- url     : https://prove2.me/theorems/b6f9e67d-02ee-463e-85c6-a2337bf9cd31
-- title:
--   Squared-norm sum of a virtual character over a cyclic-closed set is a nonnegative integer
-- statement:
--   Let $G$ be a finite group, $\varphi$ a virtual character of $G$ (that is, $\varphi\in\mathbb{Z}[\mathrm{Irr}\,G]$, the class function $\varphi:G\to\mathbb{C}$ is an integer combination of irreducible characters), and $A\subseteq G$ a finite subset that is closed under powers prime to the group order: whenever $x\in A$ and $k\in\mathbb{N}$ is coprime to $|G|$, then $x^k\in A$. Then there is a natural number $n$ with
--   $$ n=\sum_{x\in A}\|\varphi(x)\|^2 \quad(\text{as real numbers}).$$
--
--   This is the sum form of Isaacs' Lemma 3.14 / Peterfalvi (13.9.b). It makes the quantities of the form $\frac1{|G|}\sum_{x\in A}\|\lambda(x)\|^2$ appearing in the norm estimates of Peterfalvi (13.10) rational.
--
--   **Formalization Note** The class function is `ClassFunction G ℂ`, and membership in $\mathbb{Z}[\mathrm{Irr}\,G]$ is `φ ∈ ZIrr G`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Algebra/GaloisRationalInteger.lean#L216-L270

import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CyclotomicGaloisAction
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassSumAlgebra
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterConjugate
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterCompleteness
import Definitions.Def_OddOrder_Algebra_GaloisRationalInteger
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

namespace OddOrder.Algebra

open Polynomial IntermediateField

open OddOrder.RepresentationTheory in

theorem exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed {G : Type*} [Group G] [Finite G]
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) {A : Finset G}
    (hclosed : ∀ x ∈ A, ∀ k : ℕ, k.Coprime (Nat.card G) → x ^ k ∈ A) :
    ∃ n : ℕ, (n : ℝ) = ∑ x ∈ A, ‖φ x‖ ^ 2 := by sorry

end OddOrder.Algebra
