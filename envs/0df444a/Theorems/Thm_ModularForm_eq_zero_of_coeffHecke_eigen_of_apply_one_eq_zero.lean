-- Prove2me | Theorems.Thm_ModularForm_eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero
-- name    : ModularForm.eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/4d87d824-7e7d-57f6-bcf5-4041b3d0cf4b
-- title:
--   A simultaneous Hecke eigen-sequence with a₁=0 vanishes
-- statement:
--   Fix an integer $k$, a natural number $N$, and two sequences $a, c : \mathbb{N} \to \mathbb{C}$. Assume two families of eigen-equations at the level of coefficients. First, for every prime $p$ with $p \nmid N$ and every $n \in \mathbb{N}$, the quantity [`ModularForm.coeffHeckeT k p a n`](def/ModularForm_HeckeOperator.html#L162), defined as $a(np) + p^{k-1} a(n/p)$ when $p \mid n$ and as $a(np)$ otherwise (with $n/p$ the natural-number division), equals $c(p)\, a(n)$. Second, for every prime $p$ with $p \mid N$ and every $n \in \mathbb{N}$, the quantity [`ModularForm.coeffHeckeU p a n`](def/ModularForm_HeckeOperator.html#L165), defined as $a(np)$, equals $c(p)\, a(n)$. Assume finally that $a(1) = 0$. The conclusion is that $a(n) = 0$ for every $n \neq 0$. Nothing is asserted about $a(0)$, and the hypotheses are purely arithmetic conditions on the pair of sequences: no modular form, $q$-expansion or convergence is involved, and the weight $k$ enters only through the factor $p^{k-1}$.
--
--   This is the coefficient-level form of the statement that a simultaneous eigenvector for all Hecke operators is determined by its first Fourier coefficient, so that an eigen-sequence with vanishing first coefficient is identically zero away from index $0$. It is used in the construction of normalised Hecke eigenforms, being cited by [`CuspForm.exists_isNormalizedEigenform`](thm.html#CuspForm.exists_isNormalizedEigenform), [`CuspForm.exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul`](thm.html#CuspForm.exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul) and [`CuspForm.HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq`](thm.html#CuspForm.HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq), where one must know that a common Hecke eigenvector in a space of cusp forms has nonzero first $q$-coefficient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero.lean

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Complex.Basic
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero (k : ℤ) (N : ℕ) (a c : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeT k p a n = c p * a n)
    (hU : ∀ p : ℕ, p.Prime → p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeU p a n = c p * a n)
    (h1 : a 1 = 0) : ∀ n : ℕ, n ≠ 0 → a n = 0 := by sorry
