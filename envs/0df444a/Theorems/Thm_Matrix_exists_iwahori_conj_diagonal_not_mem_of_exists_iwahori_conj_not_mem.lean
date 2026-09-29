-- Prove2me | Theorems.Thm_Matrix_exists_iwahori_conj_diagonal_not_mem_of_exists_iwahori_conj_not_mem
-- name    : Matrix.exists_iwahori_conj_diagonal_not_mem_of_exists_iwahori_conj_not_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/c449dec2-8c24-57e6-891c-339b56fa144a
-- title:
--   Iwahori conjugation failure transfers to the twin maximal order
-- statement:
--   Let $p$ be a prime, let $v$ be a height-one prime of the ring of integers of $\mathbb{Q}$ containing $p$, and write $K = \mathbb{Q}_v$ for the $v$-adic completion and $\mathcal{O}$ for its valuation ring; call a matrix in $M_2(K)$ *Iwahori* when all its entries lie in $\mathcal{O}$ and, in addition, $p^{-1}$ times its $(1,0)$ entry lies in $\mathcal{O}$. Let $Y, Yi \in M_2(K)$ satisfy $Y\,Yi = 1$ and $Yi\,Y = 1$, and assume: $Y$ is Iwahori; $p \cdot Yi$ is Iwahori; $Yi$ is not Iwahori; $p^{-1}\cdot Y$ is not Iwahori; and there exists an Iwahori matrix $Z$ for which $Y Z\, Yi$ fails to have all entries in $\mathcal{O}$. The conclusion asserts the existence of an Iwahori matrix $X$ such that
--   $$\operatorname{diag}(1,p^{-1})\,(Yi\,X\,Y)\,\operatorname{diag}(1,p)$$
--   fails to have all entries in $\mathcal{O}$; that is, $Yi\,X\,Y$ does not lie in the conjugate order $\operatorname{diag}(1,p^{-1})M_2(\mathcal{O})\operatorname{diag}(1,p) = \begin{pmatrix}\mathcal{O} & p^{-1}\mathcal{O}\\ p\mathcal{O} & \mathcal{O}\end{pmatrix}$.
--
--   This is a local "type flip" at $p$ for an element $Y$ of the Iwahori order whose determinant has valuation that of $p$: failure of $Y$ to conjugate the Iwahori order into $M_2(\mathcal{O})$ forces $Y^{-1}$ to conjugate it out of the twin maximal order. It is used in the analysis of Eichler orders in quaternion algebras, feeding the two lemmas [`QuaternionAlgebra.IsEichlerOrder.exists_mem_forall_pow_smul_star_mul_mul_ne_smul_of_forall_pow_smul_mul_mul_star_ne_smul_of_inf_eq_of_dvd`](thm.html#QuaternionAlgebra.IsEichlerOrder.exists_mem_forall_pow_smul_star_mul_mul_ne_smul_of_forall_pow_smul_mul_mul_star_ne_smul_of_inf_eq_of_dvd) and [`QuaternionAlgebra.IsEichlerOrder.forall_exists_pow_smul_star_mul_mul_eq_smul_of_forall_pow_smul_mul_mul_star_ne_smul_of_inf_eq_of_dvd`](thm.html#QuaternionAlgebra.IsEichlerOrder.forall_exists_pow_smul_star_mul_mul_eq_smul_of_forall_pow_smul_mul_mul_star_ne_smul_of_inf_eq_of_dvd), and rests on the classification [`Matrix.exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori`](thm.html#Matrix.exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori) of such $Y$ into the two diagonal Iwahori double cosets and the Atkin–Lehner case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_iwahori_conj_diagonal_not_mem_of_exists_iwahori_conj_not_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem Matrix.exists_iwahori_conj_diagonal_not_mem_of_exists_iwahori_conj_not_mem
    (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (Y Yi : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (h1 : Y * Yi = 1) (h2 : Yi * Y = 1)
    (hY : ∀ i j, Y i j ∈ v.adicCompletionIntegers ℚ) (hY10 : (p : v.adicCompletion ℚ)⁻¹ * Y 1 0 ∈ v.adicCompletionIntegers ℚ)
    (hpYi : ∀ i j, ((p : v.adicCompletion ℚ) • Yi) i j ∈ v.adicCompletionIntegers ℚ)
    (hpYi10 : (p : v.adicCompletion ℚ)⁻¹ * ((p : v.adicCompletion ℚ) • Yi) 1 0 ∈ v.adicCompletionIntegers ℚ)
    (hYi : ¬ ((∀ i j, Yi i j ∈ v.adicCompletionIntegers ℚ) ∧ (p : v.adicCompletion ℚ)⁻¹ * Yi 1 0 ∈ v.adicCompletionIntegers ℚ))
    (hpY : ¬ ((∀ i j, ((p : v.adicCompletion ℚ)⁻¹ • Y) i j ∈ v.adicCompletionIntegers ℚ) ∧
      (p : v.adicCompletion ℚ)⁻¹ * ((p : v.adicCompletion ℚ)⁻¹ • Y) 1 0 ∈ v.adicCompletionIntegers ℚ))
    (hZ : ∃ Z : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), (∀ i j, Z i j ∈ v.adicCompletionIntegers ℚ) ∧ (p : v.adicCompletion ℚ)⁻¹ * Z 1 0 ∈ v.adicCompletionIntegers ℚ ∧
      ¬ ∀ i j, (Y * Z * Yi) i j ∈ v.adicCompletionIntegers ℚ) :
    ∃ X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), (∀ i j, X i j ∈ v.adicCompletionIntegers ℚ) ∧ (p : v.adicCompletion ℚ)⁻¹ * X 1 0 ∈ v.adicCompletionIntegers ℚ ∧
      ¬ ∀ i j, (Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((p : v.adicCompletion ℚ))⁻¹] * (Yi * X * Y) *
        Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)]) i j ∈ v.adicCompletionIntegers ℚ := by sorry
