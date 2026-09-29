-- Prove2me | Theorems.Thm_NumberField_FinitePlace_exists_abs_log_le_mul_neg_log_of_coe_eq
-- name    : NumberField.FinitePlace.exists_abs_log_le_mul_neg_log_of_coe_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/0a56e75d-225d-5419-8f1b-1d49685438c1
-- title:
--   Uniform bound for |log ν(z)| in terms of -log ν(p)
-- statement:
--   Fix an element $z$ of the algebraic closure $\overline{\mathbb{Q}}$ of $\mathbb{Q}$. The assertion is that there exists a real constant $C \ge 0$ such that the following holds for every intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ that is a number field, every finite place $\nu$ of $L$ in the sense of Mathlib's `NumberField.FinitePlace` (an absolute value on $L$ arising from a maximal ideal of the ring of integers), every natural number $p$ that is prime and satisfies $\nu(p) < 1$, and every $a \in L$ whose image in $\overline{\mathbb{Q}}$ equals $z$: $$|\log \nu(a)| \le C \cdot \bigl(-\log \nu(p)\bigr).$$ Here $\nu(p)$ and $\nu(a)$ denote the values of $\nu$ at the images of $p$ and at $a$ in $L$, and $\log$ is the real logarithm with Lean's convention $\log 0 = 0$, so that the case $z = 0$ is covered and gives $0 \le C\cdot(-\log\nu(p))$. The constant $C$ is chosen before $L$, $\nu$, $p$ and $a$, hence depends on $z$ alone and is uniform in the number field, the place above $p$, and the prime.
--
--   The inequality expresses that the valuation of a fixed algebraic number, measured in the unit $-\log\nu(p) > 0$ attached to a finite place $\nu$ above $p$, is bounded independently of the number field and the place; equivalently $|\mathrm{ord}_{\mathfrak{p}}(z)| \le C\,e(\mathfrak{p}/p)$. It is used in the estimates for the bad primes occurring in the Jensen-type inequality for the $j$-invariant, via [`ModularCurve.JZero.jensen_bad_primes_of_prime_of_five_le`](thm.html#ModularCurve.JZero.jensen_bad_primes_of_prime_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_FinitePlace_exists_abs_log_le_mul_neg_log_of_coe_eq.lean

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.FinitePlace.exists_abs_log_le_mul_neg_log_of_coe_eq (z : AlgebraicClosure ℚ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
      (ν : NumberField.FinitePlace ↥L) (p : ℕ), p.Prime → ν (p : ↥L) < 1 →
      ∀ a : ↥L, (a : AlgebraicClosure ℚ) = z → |Real.log (ν a)| ≤ C * (-Real.log (ν (p : ↥L))) := by sorry
