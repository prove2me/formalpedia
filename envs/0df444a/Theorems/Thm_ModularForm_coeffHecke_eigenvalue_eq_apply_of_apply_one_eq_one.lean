-- Prove2me | Theorems.Thm_ModularForm_coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one
-- name    : ModularForm.coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/c8bac6c8-5d4c-5deb-8539-030f9a4a3ba0
-- title:
--   Hecke eigenvalues of a normalised eigen-sequence are its prime coefficients
-- statement:
--   Let $k$ be an integer, $N$ a natural number, and let $a, c : \mathbb{N} \to \mathbb{C}$ be two sequences of complex numbers, $a$ playing the role of a $q$-expansion coefficient sequence and $c$ of a system of eigenvalues. Assume two families of pointwise eigen-equations. First, for every prime $p$ not dividing $N$ and every natural number $n$, $$a(np) + \bigl[\,p \mid n\,\bigr]\, p^{\,k-1} a(n/p) = c(p)\, a(n),$$ that is, the value at $n$ of [`ModularForm.coeffHeckeT k p a`](def/ModularForm_HeckeOperator.html#L162), defined as $a(np)$ plus $p^{k-1} a(n/p)$ when $p \mid n$ and plus $0$ otherwise, equals $c(p) a(n)$. Second, for every prime $p$ dividing $N$ and every $n$, the value at $n$ of [`ModularForm.coeffHeckeU p a`](def/ModularForm_HeckeOperator.html#L165), defined simply as $a(np)$, equals $c(p)a(n)$. Assume finally the normalisation $a(1) = 1$. The conclusion is that $c(p) = a(p)$ for every prime $p$.
--
--   This is the elementary statement that a normalised simultaneous Hecke eigen-sequence has its eigenvalue at $p$ equal to its $p$-th coefficient, for $T_p$ at primes away from the level and $U_p$ at primes dividing it. It feeds the construction of normalised eigenforms, being cited by [`CuspForm.exists_isNormalizedEigenform`](thm.html#CuspForm.exists_isNormalizedEigenform) and [`CuspForm.exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul`](thm.html#CuspForm.exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one.lean

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Complex.Basic
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one (k : ℤ) (N : ℕ) (a c : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeT k p a n = c p * a n)
    (hU : ∀ p : ℕ, p.Prime → p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeU p a n = c p * a n)
    (h1 : a 1 = 1) : ∀ p : ℕ, p.Prime → c p = a p := by sorry
