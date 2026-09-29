-- Prove2me | Theorems.Thm_Matrix_exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori
-- name    : Matrix.exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/82f145c2-e8ab-53de-b8f3-d56d41cb70f1
-- title:
--   Iwahori double cosets at determinant valuation one
-- statement:
--   Let $p$ be a prime and let $v$ be a height-one prime of the ring of integers of $\mathbb{Q}$ containing $p$, so that $\mathbb{Q}_v$ is the $v$-adic completion with valuation ring $\mathcal{O}_v =$ `v.adicCompletionIntegers ℚ`. Let $Y, Y_i \in M_2(\mathbb{Q}_v)$ be mutually inverse ($Y Y_i = 1$ and $Y_i Y = 1$), and assume: all entries of $Y$ lie in $\mathcal{O}_v$ and $p^{-1} Y_{10} \in \mathcal{O}_v$ (that is, $Y$ lies in the Iwahori order $\mathcal{I}$ of integral matrices with lower-left entry divisible by $p$); all entries of $p Y_i$ lie in $\mathcal{O}_v$ and $p^{-1}(p Y_i)_{10} \in \mathcal{O}_v$ (that is, $p Y^{-1} \in \mathcal{I}$); it is *not* the case that $Y_i$ is integral with $p^{-1}(Y_i)_{10} \in \mathcal{O}_v$ (that is, $Y^{-1} \notin \mathcal{I}$); and it is *not* the case that $p^{-1} Y$ is integral with $p^{-1}(p^{-1}Y)_{10} \in \mathcal{O}_v$ (that is, $p^{-1} Y \notin \mathcal{I}$). The conclusion is that $|\det Y| = |p|$ in the valuation of $\mathbb{Q}_v$, and moreover one of three alternatives holds: either there exist $\iota, \iota_i, \iota', \iota'_i \in M_2(\mathcal{O}_v)$ with $\iota\iota_i = \iota_i\iota = 1$, $\iota'\iota'_i = \iota'_i\iota' = 1$, $p^{-1}\iota_{10}, p^{-1}\iota'_{10} \in \mathcal{O}_v$ (so $\iota, \iota'$ are Iwahori units) and $Y = \iota \cdot \mathrm{diag}(p,1) \cdot \iota'$; or the same with $Y = \iota \cdot \mathrm{diag}(1,p) \cdot \iota'$; or there exist $\kappa, \kappa_i \in M_2(\mathcal{O}_v)$ with $\kappa\kappa_i = \kappa_i\kappa = 1$ and $p^{-1}\kappa_{10} \in \mathcal{O}_v$ such that $Y = \begin{pmatrix} 0 & 1 \\ p & 0\end{pmatrix} \kappa$.
--
--   This is the rank-one Iwahori–Bruhat decomposition cut down to determinant valuation one: the local Hecke conditions at Iwahori level force $Y$ into one of the two double cosets $\mathcal{I}^{\times}\mathrm{diag}(p,1)\mathcal{I}^{\times}$, $\mathcal{I}^{\times}\mathrm{diag}(1,p)\mathcal{I}^{\times}$, or into the coset of the Atkin–Lehner element $\begin{pmatrix}0&1\\p&0\end{pmatrix}$, which normalises the Iwahori order. It is used by [`Matrix.exists_iwahori_conj_diagonal_not_mem_of_exists_iwahori_conj_not_mem`](thm.html#Matrix.exists_iwahori_conj_diagonal_not_mem_of_exists_iwahori_conj_not_mem) and [`Matrix.forall_iwahori_conj_mem_of_exists_iwahori_conj_not_mem`](thm.html#Matrix.forall_iwahori_conj_mem_of_exists_iwahori_conj_not_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem Matrix.exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori
    (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (Y Yi : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (h1 : Y * Yi = 1) (h2 : Yi * Y = 1)
    (hY : ∀ i j, Y i j ∈ v.adicCompletionIntegers ℚ) (hY10 : (p : v.adicCompletion ℚ)⁻¹ * Y 1 0 ∈ v.adicCompletionIntegers ℚ)
    (hpYi : ∀ i j, ((p : v.adicCompletion ℚ) • Yi) i j ∈ v.adicCompletionIntegers ℚ) (hpYi10 : (p : v.adicCompletion ℚ)⁻¹ * ((p : v.adicCompletion ℚ) • Yi) 1 0 ∈ v.adicCompletionIntegers ℚ)
    (hYi : ¬ ((∀ i j, Yi i j ∈ v.adicCompletionIntegers ℚ) ∧ (p : v.adicCompletion ℚ)⁻¹ * Yi 1 0 ∈ v.adicCompletionIntegers ℚ))
    (hpY : ¬ ((∀ i j, ((p : v.adicCompletion ℚ)⁻¹ • Y) i j ∈ v.adicCompletionIntegers ℚ) ∧ (p : v.adicCompletion ℚ)⁻¹ * ((p : v.adicCompletion ℚ)⁻¹ • Y) 1 0 ∈ v.adicCompletionIntegers ℚ)) :
    Valued.v Y.det = Valued.v (p : v.adicCompletion ℚ) ∧
    ((∃ ι ιi ι' ι'i : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, ι i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ιi i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ι' i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ι'i i j ∈ v.adicCompletionIntegers ℚ) ∧
      ι * ιi = 1 ∧ ιi * ι = 1 ∧ ι' * ι'i = 1 ∧ ι'i * ι' = 1 ∧
      (p : v.adicCompletion ℚ)⁻¹ * ι 1 0 ∈ v.adicCompletionIntegers ℚ ∧ (p : v.adicCompletion ℚ)⁻¹ * ι' 1 0 ∈ v.adicCompletionIntegers ℚ ∧
      Y = ι * !![(p : v.adicCompletion ℚ), 0; 0, 1] * ι') ∨
     (∃ ι ιi ι' ι'i : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, ι i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ιi i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ι' i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ι'i i j ∈ v.adicCompletionIntegers ℚ) ∧
      ι * ιi = 1 ∧ ιi * ι = 1 ∧ ι' * ι'i = 1 ∧ ι'i * ι' = 1 ∧
      (p : v.adicCompletion ℚ)⁻¹ * ι 1 0 ∈ v.adicCompletionIntegers ℚ ∧ (p : v.adicCompletion ℚ)⁻¹ * ι' 1 0 ∈ v.adicCompletionIntegers ℚ ∧
      Y = ι * !![1, 0; 0, (p : v.adicCompletion ℚ)] * ι') ∨
     (∃ κ κi : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, κ i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, κi i j ∈ v.adicCompletionIntegers ℚ) ∧ κ * κi = 1 ∧ κi * κ = 1 ∧
      (p : v.adicCompletion ℚ)⁻¹ * κ 1 0 ∈ v.adicCompletionIntegers ℚ ∧ Y = !![0, 1; (p : v.adicCompletion ℚ), 0] * κ)) := by sorry
