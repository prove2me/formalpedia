-- Prove2me | Theorems.Thm_NumberField_FinitePlace_exists_finitePlace_inclusion_eq_rpow
-- name    : NumberField.FinitePlace.exists_finitePlace_inclusion_eq_rpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/03e5b46c-f995-506f-baaa-8a1d4d49038f
-- title:
--   Finite places extend, up to a positive real power
-- statement:
--   Let $L$ and $L'$ be intermediate fields of the algebraic closure $\overline{\mathbb{Q}}$ of $\mathbb{Q}$ over $\mathbb{Q}$, each of which is a number field (so each is of finite degree over $\mathbb{Q}$), and suppose $L \subseteq L'$, witnessed by $h : L \le L'$. Let $\nu$ be a finite place of $L$, i.e. an element of `NumberField.FinitePlace ↥L`, the absolute values on $L$ arising from the height-one primes of the ring of integers $\mathcal{O}_L$ in Mathlib's normalisation. The assertion is that there exist a finite place $\nu'$ of $L'$ and a real number $d$ with $0 < d$ such that for every $x \in L$ one has $\nu'(\iota(x)) = \nu(x)^d$, where $\iota$ is the field embedding `IntermediateField.inclusion h` of $L$ into $L'$ induced by the inclusion of intermediate fields. Thus $\nu$ extends to $L'$ only up to a positive real exponent: the restriction of $\nu'$ to $L$ is a power of $\nu$, not necessarily $\nu$ itself, and no information is asserted about which prime of $\mathcal{O}_{L'}$ gives $\nu'$ or about the value of $d$ (classically $d = ef$ for the prime of $L'$ above that of $\nu$).
--
--   This is the existence of an extension of a non-archimedean place to a larger number field, in the weak form in which the restriction is recovered only up to a positive real power, as is forced by Mathlib's normalisation of finite places by residue norms. It is used in the analysis of the bad primes for the $j$-invariant, in [`ModularCurve.JZero.jensen_bad_primes_of_prime_of_five_le`](thm.html#ModularCurve.JZero.jensen_bad_primes_of_prime_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_FinitePlace_exists_finitePlace_inclusion_eq_rpow.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.FinitePlace.exists_finitePlace_inclusion_eq_rpow
    {L L' : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥L] [NumberField ↥L'] (h : L ≤ L')
    (ν : NumberField.FinitePlace ↥L) :
    ∃ (ν' : NumberField.FinitePlace ↥L') (d : ℝ), 0 < d ∧
      ∀ x : ↥L, ν' (IntermediateField.inclusion h x) = ν x ^ d := by sorry
