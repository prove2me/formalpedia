-- Prove2me | Theorems.Thm_Matrix_exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers
-- name    : Matrix.exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/7ea7ed87-ea03-5f2e-a154-e7ae37984cca
-- title:
--   Elementary divisors of an integral matrix of determinant valuation 1
-- statement:
--   Fix a prime number $p$ and a height-one prime $v$ of the ring of integers $\mathcal O_{\mathbb Q}$ whose ideal contains the image of $p$; write $\mathbb Q_v$ for the $v$-adic completion of $\mathbb Q$ and $\mathcal O_v \subseteq \mathbb Q_v$ for its valuation subring, the elements of valuation at most $1$. Let $Y$ and $Yi$ be $2\times 2$ matrices over $\mathbb Q_v$ that are two-sided inverses of each other, $Y\cdot Yi = 1$ and $Yi\cdot Y = 1$. Assume that every entry of $Y$ lies in $\mathcal O_v$, that every entry of $p\,Yi$ lies in $\mathcal O_v$, but that it is not the case that all entries of $Yi$ lie in $\mathcal O_v$, and not the case that all entries of $p^{-1}Y$ lie in $\mathcal O_v$. Then there exist four $2\times 2$ matrices $K_1, K_1^{i}, K_2, K_2^{i}$ over $\mathbb Q_v$, all of whose entries lie in $\mathcal O_v$, with $K_1 K_1^{i} = K_1^{i} K_1 = 1$ and $K_2 K_2^{i} = K_2^{i} K_2 = 1$ — so that $K_1$ and $K_2$ lie in $\mathrm{GL}_2(\mathcal O_v)$ — such that $$Y = K_1 \begin{pmatrix} 1 & 0 \\ 0 & p\end{pmatrix} K_2 .$$
--
--   This is the elementary divisor (Cartan) decomposition over the discrete valuation ring $\mathcal O_v$ in the single case relevant to the Hecke operator $T_p$: the integrality hypotheses pin the valuation of $\det Y$ to exactly $1$, so the double coset of $Y$ is $\mathrm{GL}_2(\mathcal O_v)\,\mathrm{diag}(1,p)\,\mathrm{GL}_2(\mathcal O_v)$. It is obtained from the general two-by-two Cartan decomposition [`LocalGL2.exists_cartanRel_cartanDiag`](thm.html#LocalGL2.exists_cartanRel_cartanDiag) over a discrete valuation ring, and is used in the Čerednik–Drinfeld coset graph and level-$U$ Hecke computations to identify the local component at $p$ of the Hecke set defining $T_p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem Matrix.exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers
    (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (Y Yi : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (h1 : Y * Yi = 1) (h2 : Yi * Y = 1)
    (hY : ∀ i j, Y i j ∈ v.adicCompletionIntegers ℚ)
    (hpYi : ∀ i j, ((p : v.adicCompletion ℚ) • Yi) i j ∈ v.adicCompletionIntegers ℚ)
    (hYi : ¬ ∀ i j, Yi i j ∈ v.adicCompletionIntegers ℚ)
    (hpY : ¬ ∀ i j, ((p : v.adicCompletion ℚ)⁻¹ • Y) i j ∈ v.adicCompletionIntegers ℚ) :
    ∃ K₁ K₁i K₂ K₂i : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, K₁ i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, K₁i i j ∈ v.adicCompletionIntegers ℚ) ∧
      (∀ i j, K₂ i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, K₂i i j ∈ v.adicCompletionIntegers ℚ) ∧
      K₁ * K₁i = 1 ∧ K₁i * K₁ = 1 ∧ K₂ * K₂i = 1 ∧ K₂i * K₂ = 1 ∧
      Y = K₁ * !![1, 0; 0, (p : v.adicCompletion ℚ)] * K₂ := by sorry
