-- Prove2me | Theorems.Thm_ModularForm_coeffHeckeT_int
-- name    : ModularForm.coeffHeckeT_int
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/1237bd32-06f9-5159-9319-8409e716b648
-- title:
--   Integrality of the coefficient-level Hecke operator Tₚ
-- statement:
--   Let $k$ be an integer with $1 \le k$, let $p$ be a natural number, and let $a : \mathbb{N} \to \mathbb{C}$ be a sequence of complex numbers each of which is a rational integer, i.e. for every $n$ there is $m \in \mathbb{Z}$ with $a(n) = m$. Then for every natural number $n$ the value $\mathrm{coeffHeckeT}\,k\,p\,a\,n$ is again a rational integer: there exists $m \in \mathbb{Z}$ with $\mathrm{coeffHeckeT}\,k\,p\,a\,n = m$. Here [`ModularForm.coeffHeckeT`](def/ModularForm_HeckeOperator.html#L162) is defined purely in terms of the sequence by $$\mathrm{coeffHeckeT}\,k\,p\,a\,n = a(np) + \begin{cases} p^{k-1}\,a(n/p) & \text{if } p \mid n,\\ 0 & \text{otherwise,}\end{cases}$$ with $p^{k-1}$ the integer power of the complex number $p$ and $n/p$ natural-number division. No primality or positivity assumption on $p$ is made; the hypothesis $1 \le k$ serves only to ensure that the exponent $k-1$ is non-negative, so that $p^{k-1}$ is itself a non-negative integer.
--
--   This is the statement that the Hecke operator $T_p$, written on the level of $q$-expansion coefficients, preserves sequences with integral coefficients. It is used by [`CuspForm.mem_intLattice_of_coe_eq_heckeT`](thm.html#CuspForm.mem_intLattice_of_coe_eq_heckeT) to show that the lattice of cusp forms with integral Fourier coefficients is stable under $T_p$, a step towards integrality of Hecke eigenvalues.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_coeffHeckeT_int.lean

import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.coeffHeckeT_int (k : ℤ) (hk : 1 ≤ k) (p : ℕ) {a : ℕ → ℂ} (ha : ∀ n : ℕ, ∃ m : ℤ, a n = m) (n : ℕ) : ∃ m : ℤ, ModularForm.coeffHeckeT k p a n = m := by sorry
