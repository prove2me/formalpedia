-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_sum_cpow_mul_eval_eq_cpow_mul_eval
-- name    : LanglandsTunnell.RankinSelberg.exists_sum_cpow_mul_eval_eq_cpow_mul_eval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/dc5b7270-b7fd-500d-9632-0e55e2327f23
-- title:
--   Finite sums of N^{ms}P(N^{-s}) are again of that form
-- statement:
--   Let $N$ be a natural number with $N \neq 0$, let $\iota$ be a finite type, and for each $i : \iota$ let $m_i \in \mathbb{Z}$ and $P_i \in \mathbb{C}[X]$. The assertion is that there exist an integer $m_0$ and a polynomial $P_0 \in \mathbb{C}[X]$ such that for every $s \in \mathbb{C}$,
--   $$\sum_{i} N^{m_i s}\, P_i\!\left(N^{-s}\right) = N^{m_0 s}\, P_0\!\left(N^{-s}\right),$$
--   where the powers are complex powers of the complex number $N$ with exponents $m_i s$, $m_0 s$ and $-s$ (the integers $m_i$, $m_0$ being cast into $\mathbb{C}$), and the sum runs over all of $\iota$. The identity is required to hold at every complex $s$, with no exclusion of branch points; the empty type and the case $N = 1$ are included.
--
--   This is the elementary bookkeeping lemma that closes the class of functions of the shape $N^{ms}$ times a polynomial in $N^{-s}$ — equivalently Laurent polynomials in $N^{-s}$ with a single monomial prefactor — under finite sums. It is used when an unfolded local Rankin–Selberg integral is computed termwise, each term being of this shape, in order to present the total as a single expression of the same shape; it feeds the statement about local integrals of Jacquet–Whittaker and central Tate type over a chamber.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_sum_cpow_mul_eval_eq_cpow_mul_eval.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.RankinSelberg.exists_sum_cpow_mul_eval_eq_cpow_mul_eval
    (N : ℕ) (hN : N ≠ 0) (ι : Type) [Fintype ι] (m : ι → ℤ) (P : ι → Polynomial ℂ) :
    ∃ (m₀ : ℤ) (P₀ : Polynomial ℂ), ∀ s : ℂ,
      ∑ i, (N : ℂ) ^ ((m i : ℂ) * s) * (P i).eval ((N : ℂ) ^ (-s)) =
        (N : ℂ) ^ ((m₀ : ℂ) * s) * P₀.eval ((N : ℂ) ^ (-s)) := by sorry
