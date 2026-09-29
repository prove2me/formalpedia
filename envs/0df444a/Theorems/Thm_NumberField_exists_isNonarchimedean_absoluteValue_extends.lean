-- Prove2me | Theorems.Thm_NumberField_exists_isNonarchimedean_absoluteValue_extends
-- name    : NumberField.exists_isNonarchimedean_absoluteValue_extends
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/3a59f80e-3fd6-5ccc-a265-4f78c02fc0c5
-- title:
--   Finite places of number fields extend to ℚ̄
-- statement:
--   Let $L$ be an intermediate field of the extension $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$, where $\overline{\mathbb{Q}}$ denotes Mathlib's `AlgebraicClosure ℚ`, and assume $L$ is a number field, i.e. of finite degree over $\mathbb{Q}$. Let $\nu$ be a finite place of $L$, that is, an element of `NumberField.FinitePlace ↥L`: an absolute value on $L$ obtained from the norm of the completion of $L$ at a height-one prime of its ring of integers, viewed as a function on $L$ with real values. The assertion is that there exists a real-valued absolute value $\mu$ on $\overline{\mathbb{Q}}$ which is nonarchimedean, in the sense that $\mu(x+y) \le \max(\mu x, \mu y)$ for all $x, y \in \overline{\mathbb{Q}}$, and whose restriction to $L$ along the inclusion $L \hookrightarrow \overline{\mathbb{Q}}$ agrees with $\nu$ on the nose: $\mu(a) = \nu(a)$ for every $a \in L$. Only existence is asserted; no uniqueness or count of such extensions is claimed, and $\mu$ is not required to be a valuation of any prescribed normalisation beyond agreeing with $\nu$ on $L$.
--
--   This is the standard extension theorem for nonarchimedean absolute values from a number field to an algebraic closure, here in the concrete form needed to regard a finite place of a number field as a place of $\overline{\mathbb{Q}}$. It is used in the Jensen-type estimates for the $j$-line, [`ModularCurve.JZero.jensen_bad_at_le`](thm.html#ModularCurve.JZero.jensen_bad_at_le), [`ModularCurve.JZero.jensen_bad_at_of_prime_of_five_le`](thm.html#ModularCurve.JZero.jensen_bad_at_of_prime_of_five_le) and [`ModularCurve.JZero.jensen_good_at_le`](thm.html#ModularCurve.JZero.jensen_good_at_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_isNonarchimedean_absoluteValue_extends.lean

import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.exists_isNonarchimedean_absoluteValue_extends
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L] (ν : NumberField.FinitePlace ↥L) :
    ∃ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ ∧
      ∀ a : ↥L, μ (a : AlgebraicClosure ℚ) = ν a := by sorry
