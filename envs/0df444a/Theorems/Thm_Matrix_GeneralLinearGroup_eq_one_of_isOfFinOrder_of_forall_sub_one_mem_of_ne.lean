-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_eq_one_of_isOfFinOrder_of_forall_sub_one_mem_of_ne
-- name    : Matrix.GeneralLinearGroup.eq_one_of_isOfFinOrder_of_forall_sub_one_mem_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/fd91a493-5561-54c9-8507-d1ac9c58d03f
-- title:
--   Selberg's torsion-killing lemma: two primes force g=1
-- statement:
--   Let $A$ be a commutative ring that is an integral domain of characteristic zero, let $\mathfrak m_1,\mathfrak m_2$ be maximal ideals of $A$, let $p_1,p_2$ be prime natural numbers with $p_1\neq p_2$, and suppose the image of $p_1$ in $A$ lies in $\mathfrak m_1$ and the image of $p_2$ in $A$ lies in $\mathfrak m_2$. Let $n$ be a finite index type and let $g$ be a unit of the ring of $n\times n$ matrices over $A$, i.e. an element of $\mathrm{GL}_n(A)$, which is of finite order in that group. Assume that $g$ is congruent to the identity matrix entrywise modulo each of the two maximal ideals: for all indices $i,j$, the entry $g_{ij}-\delta_{ij}$ lies in $\mathfrak m_1$, and likewise for all $i,j$ the entry $g_{ij}-\delta_{ij}$ lies in $\mathfrak m_2$. The conclusion is that $g$ is the identity element of $\mathrm{GL}_n(A)$.
--
--   This is the torsion-killing step of Selberg's lemma in Alperin's form with two residue characteristics: a finite-order matrix congruent to the identity modulo two maximal ideals containing distinct rational primes is trivial. It is used in the proof that a finitely generated subgroup of $\mathrm{GL}_n(A)$ has a normal subgroup of finite index containing no nontrivial element of finite order.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_GeneralLinearGroup_eq_one_of_isOfFinOrder_of_forall_sub_one_mem_of_ne.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem Matrix.GeneralLinearGroup.eq_one_of_isOfFinOrder_of_forall_sub_one_mem_of_ne
    (A : Type) [CommRing A] [IsDomain A] [CharZero A]
    (𝔪₁ 𝔪₂ : Ideal A) (h𝔪₁ : 𝔪₁.IsMaximal) (h𝔪₂ : 𝔪₂.IsMaximal)
    (p₁ p₂ : ℕ) (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hne : p₁ ≠ p₂) (hp₁𝔪 : (p₁ : A) ∈ 𝔪₁) (hp₂𝔪 : (p₂ : A) ∈ 𝔪₂)
    (n : Type) [Fintype n] [DecidableEq n]
    (g : Matrix.GeneralLinearGroup n A) (hg : IsOfFinOrder g)
    (hg₁ : ∀ i j : n, (g : Matrix n n A) i j - (1 : Matrix n n A) i j ∈ 𝔪₁)
    (hg₂ : ∀ i j : n, (g : Matrix n n A) i j - (1 : Matrix n n A) i j ∈ 𝔪₂) :
    g = 1 := by sorry
