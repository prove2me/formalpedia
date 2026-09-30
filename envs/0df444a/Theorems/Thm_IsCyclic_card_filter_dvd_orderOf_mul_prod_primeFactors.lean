-- Prove2me | Theorems.Thm_IsCyclic_card_filter_dvd_orderOf_mul_prod_primeFactors
-- name    : IsCyclic.card_filter_dvd_orderOf_mul_prod_primeFactors
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:06:06.309962+00:00
-- url     : https://prove2.me/theorems/41c0a834-f0f3-4d4b-8262-96f75816839e
-- title:
--   The number of elements of a cyclic group whose order is a multiple of f
-- statement:
--   Let $G$ be a finite cyclic group of order $h$, and let $f\in\mathbb N$ divide $h$. Put $C_f=\{g\in G:f\mid\operatorname{ord}(g)\}$ and $a_p=v_p(h)-v_p(f)+1$ for each prime $p\mid f$.
--
--   $$
--   |C_f|\prod_{p\mid f}p^{a_p}=h\prod_{p\mid f}(p^{a_p}-1).
--   $$
--
--   This is a denominator-free counting formula for elements whose orders contain a prescribed divisor.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/GroupTheory/SpecificGroups/Cyclic/OrderCount.lean#L151-L224), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/GroupTheory/SpecificGroups/Cyclic/OrderCount.lean#L151-L224

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Counting the elements of a cyclic group by a condition on their order

In a finite cyclic group, the number of elements whose order satisfies a predicate `p` is the sum
of `φ d` over the divisors `d` of the group order that satisfy `p`.

Mathlib counts elements of an *exact* order: `IsCyclic.card_orderOf_eq_totient` says there are
`φ d` of them for each `d` dividing the group order. Summing that over the divisors selected by
`p` is the whole content here.

The point of stating it for a predicate is that it turns a count defined by a condition on orders
into an arithmetic sum over divisors, where the group has disappeared. Whatever `p` is, the answer
is a totient sum over `{d ∣ #α | p d}`, so it can then be evaluated or estimated by number theory
alone.

## Main results

* `IsCyclic.card_filter_orderOf_eq_sum_totient`, and its additive counterpart: the count of
  elements whose order satisfies `p` is `∑ φ d` over the divisors `d` of the group order with
  `p d`.
* `IsCyclic.card_filter_dvd_orderOf_eq_sum_totient`: the case `p = (f ∣ ·)`.
* `IsCyclic.card_filter_dvd_orderOf_mul_prod_primeFactors`, and its additive counterpart: that
  case in closed form, in `ℕ`.
* `IsCyclic.card_filter_dvd_orderOf_eq_mul_prod_primeFactors`, and its additive counterpart: the
  closed form as a product over `ℚ`.
* `IsCyclic.le_card_filter_dvd_orderOf`, and its additive counterpart: the uniform lower bound
  `(1 - 2 ^ -r) ^ #f.primeFactors` for the proportion of elements of order divisible by `f`, when
  `f ^ r ∣ #α`.

## The elements of order divisible by `f`, in closed form

Let `α` have order `h` and let `f` divide `h`. The elements of `α` whose order is a multiple of
`f` are counted exactly:

`#{τ | f ∣ orderOf τ} = h * ∏ p ∣ f, (1 - p ^ -(v_p h - v_p f + 1))`,

the product running over the primes of `f`. Writing `τ = g ^ k` for a generator `g`, `f` divides
the order of `τ` exactly when `p ^ (v_p h - v_p f + 1)` fails to divide `k` for every prime `p` of
`f` (`IsOfFinOrder.dvd_orderOf_pow_iff`). Those conditions constrain `k` modulo coprime prime
powers, so they are independent and the count is a product.

Two forms of the count are recorded: an identity in `ℕ`, cleared of denominators, and the
displayed product over `ℚ`. At `f = h` every exponent is `1` and the count becomes Euler's
product formula `Nat.totient_mul_prod_primeFactors`, since the elements whose order is a multiple
of `h` are the `φ h` generators.

The third result is the estimate that makes the count usable when `f` is fixed and `h` is
divisible by a high power of `f`: if `f ^ r ∣ h` with `1 ≤ r`, every factor of the product is at
least `1 - 2 ^ -r`, so the proportion of elements of order divisible by `f` is at least
`(1 - 2 ^ -r) ^ #f.primeFactors`, which tends to `1` as `r` grows.
-/

 section

open Finset Nat

open scoped Function -- for the `on` notation in `Pairwise (Nat.Coprime on a)`

variable {α : Type*} [Group α] [Fintype α] [IsCyclic α]





namespace IsCyclic
end IsCyclic
section IsCyclic
open IsCyclic

variable {f : ℕ}

theorem IsCyclic.card_filter_dvd_orderOf_mul_prod_primeFactors (hf : f ∣ _root_.Fintype.card α) :
    #{τ : α | f ∣ _root_.orderOf τ} *
        ∏ p ∈ f.primeFactors,
          p ^ ((_root_.Fintype.card α).factorization p - f.factorization p + 1)
      = _root_.Fintype.card α *
        ∏ p ∈ f.primeFactors,
          (p ^ ((_root_.Fintype.card α).factorization p - f.factorization p + 1) - 1) := by sorry
