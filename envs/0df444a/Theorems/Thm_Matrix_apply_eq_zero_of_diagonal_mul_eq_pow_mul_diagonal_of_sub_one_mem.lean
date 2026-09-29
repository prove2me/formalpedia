-- Prove2me | Theorems.Thm_Matrix_apply_eq_zero_of_diagonal_mul_eq_pow_mul_diagonal_of_sub_one_mem
-- name    : Matrix.apply_eq_zero_of_diagonal_mul_eq_pow_mul_diagonal_of_sub_one_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/ec7fe90a-c69d-5b22-87aa-bbea6bbf24ce
-- title:
--   Off-diagonal entries vanish under a tame matrix relation
-- statement:
--   Let $A$ be a commutative local ring with maximal ideal $\mathfrak m =$ `IsLocalRing.maximalIdeal A`, and assume $A$ is $\mathfrak m$-adically separated in the form: every $x \in A$ lying in $\mathfrak m^n$ for all $n \in \mathbb N$ is $0$. Let $a, d \in A$ and $q \in \mathbb N$ be such that both $a - q\,d$ and $d - q\,a$ are units of $A$ (here $q$ denotes the image of the natural number $q$ in $A$). Let $N$ be a $2 \times 2$ matrix over $A$ whose entries are congruent to those of the identity matrix modulo $\mathfrak m$, i.e. $N_{ij} - \delta_{ij} \in \mathfrak m$ for all $i, j \in \{0,1\}$, and suppose the relation
--   $$\operatorname{diag}(a,d)\, N = N^{q}\, \operatorname{diag}(a,d)$$
--   holds in $M_2(A)$, where $\operatorname{diag}(a,d)$ is the diagonal matrix with entries $a, d$ taken from the vector $![a,d]$. Then the two off-diagonal entries of $N$ vanish: $N_{01} = 0$ and $N_{10} = 0$.
--
--   This is the Nakayama-type step in the proof of Lemma 2.44 of Darmon–Diamond–Taylor, where $\operatorname{diag}(a,d)$ is the value of a lift at a Frobenius element in an eigenbasis, $N$ the value at an element of tame inertia, and the displayed identity the tame relation; the conclusion is that the inertia matrix is diagonal. It is used in the basis-free reformulation [`LinearMap.exists_apply_basis_eq_smul_of_mul_eq_pow_mul_of_toMatrix_sub_one_mem`](thm.html#LinearMap.exists_apply_basis_eq_smul_of_mul_eq_pow_mul_of_toMatrix_sub_one_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_apply_eq_zero_of_diagonal_mul_eq_pow_mul_diagonal_of_sub_one_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Matrix.apply_eq_zero_of_diagonal_mul_eq_pow_mul_diagonal_of_sub_one_mem {A : Type u} [CommRing A] [IsLocalRing A]
    (hH : ∀ x : A, (∀ n : ℕ, x ∈ IsLocalRing.maximalIdeal A ^ n) → x = 0)
    {a d : A} {q : ℕ} (had : IsUnit (a - (q : A) * d)) (hda : IsUnit (d - (q : A) * a))
    {N : Matrix (Fin 2) (Fin 2) A} (hN : ∀ i j, N i j - (1 : Matrix (Fin 2) (Fin 2) A) i j ∈ IsLocalRing.maximalIdeal A)
    (hrel : Matrix.diagonal ![a, d] * N = N ^ q * Matrix.diagonal ![a, d]) :
    N 0 1 = 0 ∧ N 1 0 = 0 := by sorry
