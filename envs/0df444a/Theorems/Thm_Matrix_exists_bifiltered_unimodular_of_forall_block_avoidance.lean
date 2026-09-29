-- Prove2me | Theorems.Thm_Matrix_exists_bifiltered_unimodular_of_forall_block_avoidance
-- name    : Matrix.exists_bifiltered_unimodular_of_forall_block_avoidance
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/85867c8a-5855-56aa-b83a-6ff20a548fd3
-- title:
--   Existence of bifiltered p-unimodular matrices avoiding affine conditions
-- statement:
--   Let $p$ be a prime, $r$ a natural number and $n \colon \mathrm{Fin}\,r \to \mathbb{N}$ a function with $n_i = 0$ whenever the index $i$ is $0$. For each $i$ let $\iota_i$ be a finite type and, for each $j \in \iota_i$, let $V_{i,j}$ be a $\mathbb{Z}/p$-module and $\varphi_{i,j} \colon (\mathrm{Fin}\,r \to \mathbb{Z}/p) \to V_{i,j}$ an affine map over $\mathbb{Z}/p$. Assume that for every $i \neq 0$ and every $j$ the map $\varphi_{i,j}$ is not identically zero, and that $\#\iota_i + 1 < p$ for all $i$. Then there exist a matrix $U \in \mathrm{Matrix}(\mathrm{Fin}\,r, \mathrm{Fin}\,r, \mathbb{Q})$ and digits $d \colon \mathrm{Fin}\,r \to \mathrm{Fin}\,r \to \mathbb{Z}/p$ such that: $U$ is a unit in the matrix ring over $\mathbb{Q}$; for all $i,j$ either $U_{ij} = 0$ or $\mathrm{padicValRat}_p(U_{ij}) \geq \max(0, n_i - n_j)$ (as integers), and likewise for the entries of the inverse $U^{-1}$; the row of $U$ of index $0$ is the first standard basis vector, i.e. $U_{0j}$ is $1$ if $j = 0$ and $0$ otherwise; every entry satisfies $U_{ij} = p^{\max(0, n_i - n_j)} \cdot \tilde d_{ij}$, where $\tilde d_{ij} \in \{0,\dots,p-1\}$ is the canonical representative of $d_{ij}$ viewed in $\mathbb{Q}$ and the exponent is the natural number associated with $\max(0, n_i - n_j)$; for every $c \in \mathbb{N}$ the square submatrix of $d$ with rows and columns indexed by $\{a : n_a = c\}$ has determinant a unit in $\mathbb{Z}/p$; and $\varphi_{i,j}(d_i) \neq 0$ for every $i \neq 0$ and every $j$, where $d_i \colon \mathrm{Fin}\,r \to \mathbb{Z}/p$ is the $i$-th row of $d$.
--
--   This is an elementary linear-algebra existence statement: a rational matrix which is $p$-adically unimodular in a bifiltered sense (both $U$ and $U^{-1}$ have entries of valuation at least $\max(0, n_i - n_j)$), is normalised in its zeroth row, has prescribed digit shape, invertible diagonal blocks over $\mathbb{Z}/p$, and whose rows avoid finitely many prescribed affine conditions. It is used to produce unimodular recombination matrices in [`ModularCurve.MultCovering.exists_unimodular_famData_wideCertificates`](thm.html#ModularCurve.MultCovering.exists_unimodular_famData_wideCertificates), and rests on a finite-field avoidance lemma for affine maps together with the $p$-integrality of inverses of integer matrices with determinant prime to $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_bifiltered_unimodular_of_forall_block_avoidance.lean

import Mathlib
import Theorems.Thm_FiniteField_exists_forall_affineMap_apply_ne_zero_of_forall_lt
import Theorems.Thm_Matrix_isUnit_and_padicValRat_inv_nonneg_of_not_dvd_det

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Matrix.exists_bifiltered_unimodular_of_forall_block_avoidance
    (p : ℕ) [Fact p.Prime] {r : ℕ} (n : Fin r → ℕ) (hn0 : ∀ i : Fin r, (i : ℕ) = 0 → n i = 0)
    {ι : Fin r → Type*} [∀ i, Fintype (ι i)]
    {V : ∀ i, ι i → Type*} [∀ i j, AddCommGroup (V i j)] [∀ i j, Module (ZMod p) (V i j)]
    (φ : ∀ i j, (Fin r → ZMod p) →ᵃ[ZMod p] V i j)
    (hφ : ∀ i : Fin r, (i : ℕ) ≠ 0 → ∀ j, ∃ x, φ i j x ≠ 0)
    (hm : ∀ i, Fintype.card (ι i) + 1 < p) :
    ∃ (U : Matrix (Fin r) (Fin r) ℚ) (d : Fin r → Fin r → ZMod p),
      IsUnit U ∧
      (∀ i j, max 0 ((n i : ℤ) - (n j : ℤ)) ≤ padicValRat p (U i j) ∨ U i j = 0) ∧
      (∀ i j, max 0 ((n i : ℤ) - (n j : ℤ)) ≤ padicValRat p (U⁻¹ i j) ∨ U⁻¹ i j = 0) ∧
      (∀ i j : Fin r, (i : ℕ) = 0 → U i j = if (j : ℕ) = 0 then 1 else 0) ∧
      (∀ i j, U i j = (p : ℚ) ^ (max 0 ((n i : ℤ) - (n j : ℤ))).toNat * ((d i j).val : ℚ)) ∧
      (∀ c : ℕ, IsUnit (Matrix.det (Matrix.of fun (i j : {a : Fin r // n a = c}) => d i.1 j.1))) ∧
      (∀ i : Fin r, (i : ℕ) ≠ 0 → ∀ j, φ i j (d i) ≠ 0) := by sorry
