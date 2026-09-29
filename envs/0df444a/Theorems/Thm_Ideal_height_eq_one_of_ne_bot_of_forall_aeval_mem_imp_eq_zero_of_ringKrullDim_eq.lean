-- Prove2me | Theorems.Thm_Ideal_height_eq_one_of_ne_bot_of_forall_aeval_mem_imp_eq_zero_of_ringKrullDim_eq
-- name    : Ideal.height_eq_one_of_ne_bot_of_forall_aeval_mem_imp_eq_zero_of_ringKrullDim_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/4b914473-8959-59df-8abb-99e19b60c8c5
-- title:
--   Nonzero prime with d independent residues has height one
-- statement:
--   Let $k$ be a field and let $A$ be a commutative ring which is an integral domain and a $k$-algebra of finite type, and let $p \subset A$ be a prime ideal with $p \neq \bot$. Assume given a natural number $d$ such that the Krull dimension of $A$, as an element of $\mathrm{WithBot}\ \mathbb{N}_\infty$, equals $d+1$, and a family $f : \mathrm{Fin}\ d \to A$ with the property that every polynomial $Q \in k[X_i : i \in \mathrm{Fin}\ d]$ whose evaluation $\mathrm{aeval}\ f\ Q$ at the $f_i$ lies in $p$ is the zero polynomial; that is, the $f_i$ are algebraically independent over $k$ modulo $p$. The conclusion is that the height of $p$ is $1$ (as an element of $\mathbb{N}_\infty$).
--
--   This is the dimension formula for affine domains in the form: on an affine domain of dimension $d+1$, a nonzero prime over which $d$ given elements stay algebraically independent is of codimension one. It is used in the construction of a proper model on which the centre of a valuation of the function field is a codimension-one point, via [`AlgebraicGeometry.exists_isProper_ringKrullDim_stalk_eq_one_of_valuationSubring_functionField`](thm.html#AlgebraicGeometry.exists_isProper_ringKrullDim_stalk_eq_one_of_valuationSubring_functionField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_height_eq_one_of_ne_bot_of_forall_aeval_mem_imp_eq_zero_of_ringKrullDim_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem Ideal.height_eq_one_of_ne_bot_of_forall_aeval_mem_imp_eq_zero_of_ringKrullDim_eq
    (k : Type u) [Field k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A]
    (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥)
    (d : ℕ) (hd : ((d + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim A)
    (f : Fin d → A) (hind : ∀ Q : MvPolynomial (Fin d) k, MvPolynomial.aeval f Q ∈ p → Q = 0) :
    p.height = 1 := by sorry
